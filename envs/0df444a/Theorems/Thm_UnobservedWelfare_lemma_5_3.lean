-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_5_3
-- name    : UnobservedWelfare.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:16.125718+00:00
-- url     : https://prove2.me/theorems/0bb96746-ade4-4820-9b48-1d170db5d62b
-- title:
--   Lemma 5.3 — inventory-penalty transfer (51)
-- statement:
--   Throughout, $c$ is an admissible cost, the buyer model on a standard Borel type space satisfies RC at scale $W>0$ and is centered ($S_\theta(1)=0$), $p^\star$ is a comparison price (34), $0<\gamma\le1$, $\kappa\ge80/\gamma$, $m,T\ge1$, and the execution (with any permitted demand selection) is of Algorithm 1.
--
--   On every path, for every $2\le t\le T$ and every $y\gg0$, with $z_t(y)=(2p_t+y)/3$,
--   $$\Gamma_{w_t}(p^I_t)\le2\gamma W\sum_{j<t}w_{jt}f(a_j(p^\star))+72\gamma\big[3F_{w_t}(z_t(y))+F_{w_t}(y)-5F_{w_t}(p^H_t)+(6m+1)W\big].\tag{51}$$
--
--   It replaces the coarse bound $\Gamma_{w_t}\le\gamma WM_t/2$ by one that can be summed over rounds.
--
--   Differences from the source:
--   - encoding: an execution of Algorithm 1 (well defined, measurable and safe by Lemmas 4.1, B.1 and 4.4) → an `Execution` (adapted processes with $q_t\in[0,1]^m$, $p_t\gg0$, $X_t\in D_{\theta_t}(p_t)$ on every path) driven by `alg1 m T W c γ κ`; reason: every execution of Algorithm 1 is such a record, by those lemmas; the records driven by `alg1` are exactly its executions
--   - encoding: rounds $t\in[T]$ → Lean round `k` is the paper round $t=k+1$; the analysis quantities take the paper index $t$; reason: index convention only
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 5.3 (51), p.28 (PDF p.30)

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

/-- **Lemma 5.3 (inventory-penalty transfer)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 5.3 (51), p.28 (PDF p.30)). Under
the standing assumptions of Sections 4–6 (p.22, p.27, p.32): an admissible cost `c`; an
i.i.d. buyer model on a standard Borel type space satisfying RC at scale `W > 0` and centered,
`S_θ(1) = 0` (p.18); a comparison price `p⋆` as in (34); `0 < γ ≤ 1` and `κ ≥ 80/γ`; and an
execution (every permitted demand selection) of Algorithm 1 with these `γ, κ`: on every path, for every paper round `2 ≤ t ≤ T` and every `y ≫ 0`, with
`z_t(y) := (2p_t + y)/3`,
`Γ_{w_t}(p^I_t) ≤ 2γW Σ_{j<t} w_{jt} f(a_j(p⋆)) + 72γ[3F_{w_t}(z_t(y)) + F_{w_t}(y) − 5F_{w_t}(p^H_t) + (6m + 1)W]`.

**Formalization Note** Record `j : Fin (t − 1)` is the paper's record `j + 1`, with weight
`w_{j+1,t}`; `a_j(p⋆)` is `affineRecord W p_j X_j p⋆` and `f` is `recCorr`. -/
theorem lemma_5_3 {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) (W γ κ : ℝ) (hW : 0 < W) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 80 / γ ≤ κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0)
    (pstar : Fin m → ℝ) (hpstar : IsComparisonPrice u P c W T pstar)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Execution m T P u μ) (hE : E.DrivenBy (alg1 m T W c γ κ)) :
    ∀ ω, ∀ t, 2 ≤ t → t ≤ T → ∀ y ∈ posOrthant m,
      E.gam W γ t ω (E.pInv W γ κ t ω) ≤
        2 * γ * W * ∑ j : Fin (t - 1),
            wts T t (t - 1) j * recCorr (affineRecord W (E.p j ω) (E.X j ω) pstar)
          + 72 * γ * (3 * E.surr W c pstar t ω ((1 / 3 : ℝ) • ((2 : ℝ) • E.p (t - 1) ω + y)) + E.surr W c pstar t ω y
            - 5 * E.surr W c pstar t ω (E.pHist W c t ω) + (6 * m + 1) * W) := by sorry

end UnobservedWelfare
