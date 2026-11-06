-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_5_5
-- name    : UnobservedWelfare.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:07.42587+00:00
-- url     : https://prove2.me/theorems/5f9cb7ea-7ddd-4eaa-9cd2-452068e75918
-- title:
--   Lemma 5.5 — common-anchor bound (55)
-- statement:
--   Throughout, $c$ is an admissible cost, the buyer model on a standard Borel type space satisfies RC at scale $W>0$ and is centered ($S_\theta(1)=0$), $p^\star$ is a comparison price (34), $0<\gamma\le1$, $\kappa\ge80/\gamma$, $m,T\ge1$, and the execution (with any permitted demand selection) is of Algorithm 1.
--
--   For every $2\le t\le T$: $\mathbb E[\Lambda_t]\le1$, $0<\Lambda_t<\infty$ almost surely, and on a single event of probability one, simultaneously for all $p\gg0$,
--   $$3F_{w_t}\Big(\frac{2p+\bar y_t}{3}\Big)+F_{w_t}(\bar y_t)\le3R_{M_t}(p)+(3\log3+2)mW+3W+4W\log\Lambda_t,\tag{55}$$
--   where $\bar y_t$ is the mean of $\Pi_t=\pi^{R_{M_t}}_{2W}$.
--
--   One random scalar $\Lambda_t$ thus controls the history score at every price, including the adaptive price $p_t$.
--
--   Differences from the source:
--   - encoding: $\Lambda_t$ and $\log\Lambda_t$ → $\Lambda_t$ is a $[0,\infty]$-valued lower integral; $\log\Lambda_t$ is the real logarithm of its real value; reason: on the almost-sure event $0<\Lambda_t<\infty$ these agree
--   - encoding: an execution of Algorithm 1 (well defined, measurable and safe by Lemmas 4.1, B.1 and 4.4) → an `Execution` (adapted processes with $q_t\in[0,1]^m$, $p_t\gg0$, $X_t\in D_{\theta_t}(p_t)$ on every path) driven by `alg1 m T W c γ κ`; reason: every execution of Algorithm 1 is such a record, by those lemmas; the records driven by `alg1` are exactly its executions
--   - encoding: rounds $t\in[T]$ → Lean round `k` is the paper round $t=k+1$; the analysis quantities take the paper index $t$; reason: index convention only
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 5.5 (55), p.30 (PDF p.32)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret
import Definitions.Def_UnobservedWelfare_gibbsMean
import Definitions.Def_UnobservedWelfare_alg1
import Definitions.Def_UnobservedWelfare_roundLoss
import Definitions.Def_UnobservedWelfare_potential

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma 5.5 (common-anchor bound)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 5.5 (55), p.30 (PDF p.32)). Under
the standing assumptions of Sections 4–6 (p.22, p.27, p.32): an admissible cost `c`; an
i.i.d. buyer model on a standard Borel type space satisfying RC at scale `W > 0` and centered,
`S_θ(1) = 0` (p.18); a comparison price `p⋆` as in (34); `0 < γ ≤ 1` and `κ ≥ 80/γ`; and an
execution (every permitted demand selection) of Algorithm 1 with these `γ, κ`: for every `2 ≤ t ≤ T`, `E[Λ_t] ≤ 1` and `0 < Λ_t < ∞` almost surely, and on a single
event of probability one, simultaneously for all `p ≫ 0`,
`3F_{w_t}((2p + ȳ_t)/3) + F_{w_t}(ȳ_t) ≤ 3R_{M_t}(p) + (3 log 3 + 2)mW + 3W + 4W log Λ_t`,
where `Π_t = π^{R_{M_t}}_{2W}`, `ȳ_t = E_{Π_t}[Y]` and `Λ_t = E_{Π_t}[e^{[F_{w_t}(Y) − R_{M_t}(Y)]/W}]`.

**Formalization Note** `Λ_t` is `Execution.anchor`, valued in `[0, ∞]`; on the almost-sure event
where it is positive and finite, `log Λ_t` is the real logarithm of its real value. The bound (55)
is `∀ᵐ ω, ∀ p ≫ 0, …`: one null set for all prices. -/
theorem lemma_5_5 {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) (W γ κ : ℝ) (hW : 0 < W) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 80 / γ ≤ κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0)
    (pstar : Fin m → ℝ) (hpstar : IsComparisonPrice u P c W T pstar)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Execution m T P u μ) (hE : E.DrivenBy (alg1 m T W c γ κ)) :
    ∀ t, 2 ≤ t → t ≤ T →
      ∫⁻ ω, E.anchor W c pstar t ω ∂μ ≤ 1 ∧
      (∀ᵐ ω ∂μ, 0 < E.anchor W c pstar t ω ∧ E.anchor W c pstar t ω < ⊤) ∧
      ∀ᵐ ω ∂μ, ∀ p ∈ posOrthant m,
        3 * E.surr W c pstar t ω ((1 / 3 : ℝ) • ((2 : ℝ) • p + gibbsMean (2 * W) (popEnergy u P c W T pstar (mass T t))))
          + E.surr W c pstar t ω (gibbsMean (2 * W) (popEnergy u P c W T pstar (mass T t)))
        ≤ 3 * popEnergy u P c W T pstar (mass T t) p + (3 * Real.log 3 + 2) * m * W + 3 * W
          + 4 * W * Real.log (E.anchor W c pstar t ω).toReal := by sorry

end UnobservedWelfare
