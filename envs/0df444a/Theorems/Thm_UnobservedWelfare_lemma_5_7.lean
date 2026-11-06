-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_5_7
-- name    : UnobservedWelfare.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:12.822856+00:00
-- url     : https://prove2.me/theorems/185275ab-3ac5-4b43-8ff3-70dc0f8b1912
-- title:
--   Lemma 5.7 — summed forgetting error (estimate (II) with $C=6$)
-- statement:
--   Throughout, $c$ is an admissible cost, the buyer model on a standard Borel type space satisfies RC at scale $W>0$ and is centered ($S_\theta(1)=0$), $p^\star$ is a comparison price (34), $0<\gamma\le1/1732$, $\kappa\ge80/\gamma$, $m,T\ge1$, and the execution (with any permitted demand selection) is of Algorithm 1.
--
--   Then $L_t$ ($t\in[T]$) and $E_t$ ($2\le t\le T$) are integrable and
--   $$\sum_{t=2}^T\rho_t\mathbb E[E_t]\le\frac12\mathbb E\Big[\sum_{t=1}^TL_t\Big]+6mW\sum_{t=2}^T\rho_t.$$
--   Thus estimate (II) of Lemma 3.2 holds with $C=6$.
--
--   Differences from the source:
--   - generalization: the summed inequality → the summed inequality together with integrability of $L_t$ and $E_t$; reason: this integrability is the paper Lemma 4.4; dropping it gives the source statement
--   - encoding: an execution of Algorithm 1 (well defined, measurable and safe by Lemmas 4.1, B.1 and 4.4) → an `Execution` (adapted processes with $q_t\in[0,1]^m$, $p_t\gg0$, $X_t\in D_{\theta_t}(p_t)$ on every path) driven by `alg1 m T W c γ κ`; reason: every execution of Algorithm 1 is such a record, by those lemmas; the records driven by `alg1` are exactly its executions
--   - encoding: rounds $t\in[T]$ → Lean round `k` is the paper round $t=k+1$; the analysis quantities take the paper index $t$; reason: index convention only
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 5.7, p.31 (PDF p.33)

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

/-- **Lemma 5.7 (summed forgetting error; estimate (II))** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 5.7, p.31 (PDF p.33)).
Under the standing assumptions of Sections 4–6 (p.22, p.27, p.32): an admissible cost `c`; an
i.i.d. buyer model on a standard Borel type space satisfying RC at scale `W > 0` and centered,
`S_θ(1) = 0` (p.18); a comparison price `p⋆` as in (34); `0 < γ ≤ 1` and `κ ≥ 80/γ`; and an
execution (every permitted demand selection) of Algorithm 1 with these `γ, κ`, if moreover `0 < γ ≤ 1/1732`, then
`Σ_{t=2}^T ρ_t E[E_t] ≤ (1/2) E[Σ_{t=1}^T L_t] + 6mW Σ_{t=2}^T ρ_t`; thus estimate (II) of
Lemma 3.2 holds with `C = 6`.

**Formalization Note** `γ ≤ 1/1732` replaces the standing `γ ≤ 1`, which it implies. The
conclusion records the integrability of `L_t` and `E_t` (the paper's Lemma 4.4), so that the
expectations are not junk values. -/
theorem lemma_5_7 {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) (W γ κ : ℝ) (hW : 0 < W) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1 / 1732) (hκ : 80 / γ ≤ κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0)
    (pstar : Fin m → ℝ) (hpstar : IsComparisonPrice u P c W T pstar)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Execution m T P u μ) (hE : E.DrivenBy (alg1 m T W c γ κ)) :
    (∀ t, 1 ≤ t → t ≤ T → Integrable (E.roundLoss c W pstar t) μ) ∧
    (∀ t, 2 ≤ t → t ≤ T → Integrable (E.forgettingError W γ κ c pstar t) μ) ∧
    ∑ t ∈ Finset.Icc 2 T, rho T t * ∫ ω, E.forgettingError W γ κ c pstar t ω ∂μ ≤
      1 / 2 * ∫ ω, ∑ t ∈ Finset.Icc 1 T, E.roundLoss c W pstar t ω ∂μ
        + 6 * m * W * ∑ t ∈ Finset.Icc 2 T, rho T t := by sorry

end UnobservedWelfare
