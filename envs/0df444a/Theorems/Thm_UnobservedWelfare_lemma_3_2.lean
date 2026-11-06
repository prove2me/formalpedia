-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_3_2
-- name    : UnobservedWelfare.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:57.493967+00:00
-- url     : https://prove2.me/theorems/0be4c160-e216-47e7-b822-b7074e846680
-- title:
--   Lemma 3.2 — three estimates imply $\mathrm{Reg}_T\le12CmW[1+\log(T+1)]$
-- statement:
--   Let $c$ be admissible, the buyer model centered and RC at scale $W$, and $p^\star$ a comparison price. Consider a safe execution (of any policy) with integrable losses $L_t$. Let $\Psi_t$ be an integrable $\mathcal F_t$-measurable random variable for each $t\in[T]$ and $E_t$ an integrable $\mathcal F_{t-1}$-measurable random variable for $2\le t\le T$. Suppose that for some constant $C>0$:
--
--   1. (I) cumulative drift: $\mathbb E[L_1+\Psi_1]\le CmW$ and $\mathbb E[L_t+\Psi_t-\Psi_{t-1}\mid\mathcal F_{t-1}]\le\rho_tE_t+CmW\rho_t$ for $2\le t\le T$;
--   2. (II) forgetting error: $\sum_{t=2}^T\rho_t\mathbb E[E_t]\le\frac12\mathbb E\big[\sum_{t=1}^TL_t\big]+CmW\sum_{t=2}^T\rho_t$;
--   3. (III) terminal potential: $\mathbb E[p^\star\cdot I_T-\Psi_T]\le CmW[1+\log(T+1)]$.
--
--   Then
--   $$\mathrm{Reg}_T\le12CmW[1+\log(T+1)].$$
--
--   This reduces Theorem 3.1 to the three estimates proved in Sections 4–6.
--
--   Differences from the source:
--   - reading: "for some constant $C>0$ independent of $m,T,W$" → any $C>0$ (with $m,T,W$ fixed in the statement); reason: independence is a uniformity remark about how the lemma is applied; for fixed $m,T,W$ the hypothesis is a single constant
--   - encoding: conditional inequalities in (I) → `condExp` inequalities holding $\mu$-almost surely; reason: conditional expectations are defined up to null sets
--   - encoding: rounds $t\in[T]$ → Lean round `k` is the paper round $t=k+1$; the analysis quantities take the paper index $t$; reason: index convention only
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 3.2, pp.21–22 (PDF pp.23–24)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret
import Definitions.Def_UnobservedWelfare_alg1
import Definitions.Def_UnobservedWelfare_roundLoss

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma 3.2 (three-estimate framework)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 3.2, pp.21–22 (PDF pp.23–24)). Consider
a safe execution with integrable losses `L_t`, for a centered buyer model satisfying RC at scale
`W`, an admissible cost and a comparison price `p⋆` as in (34). Let `Ψ_t` be an integrable,
`F_t`-measurable random variable for each `t ∈ [T]`, and `E_t` an integrable, `F_{t−1}`-measurable
random variable for `2 ≤ t ≤ T`. Suppose that, for some constant `C > 0`:
(I) `E[L_1 + Ψ_1] ≤ CmW` and `E[L_t + Ψ_t − Ψ_{t−1} | F_{t−1}] ≤ ρ_t E_t + CmWρ_t` (`2 ≤ t ≤ T`);
(II) `Σ_{t=2}^T ρ_t E[E_t] ≤ (1/2)E[Σ_{t=1}^T L_t] + CmW Σ_{t=2}^T ρ_t`;
(III) `E[p⋆·I_T − Ψ_T] ≤ CmW[1 + log(T + 1)]`.
Then `Reg_T ≤ 12CmW[1 + log(T + 1)]`.

**Formalization Note** The execution is of any policy (no policy appears). "`C` independent of
`m, T, W`" is a remark about uniformity; with `m, T, W` fixed it is any `C > 0`. The conditional
inequalities hold almost surely. `p⋆·I_T` is integrable without a separate hypothesis: on a safe
execution `0 ≤ I_T ≤ Σ_t q_t ≤ T·1` and `I_T` is measurable, so the expectation in (III) is a genuine
one. -/
theorem lemma_3_2 {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) (W : ℝ) (hW : 0 < W)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0)
    (pstar : Fin m → ℝ) (hpstar : IsComparisonPrice u P c W T pstar)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Execution m T P u μ) (hsafe : E.IsSafe)
    (hL : ∀ t, 1 ≤ t → t ≤ T → Integrable (E.roundLoss c W pstar t) μ)
    (Ψ : ℕ → Ω → ℝ) (hΨi : ∀ t, 1 ≤ t → t ≤ T → Integrable (Ψ t) μ)
    (hΨm : ∀ t, 1 ≤ t → t ≤ T → Measurable[E.fil t] (Ψ t))
    (Er : ℕ → Ω → ℝ) (hEri : ∀ t, 2 ≤ t → t ≤ T → Integrable (Er t) μ)
    (hErm : ∀ t, 2 ≤ t → t ≤ T → Measurable[E.fil (t - 1)] (Er t))
    (C : ℝ) (hC : 0 < C)
    (hI1 : ∫ ω, E.roundLoss c W pstar 1 ω + Ψ 1 ω ∂μ ≤ C * m * W)
    (hIt : ∀ t, 2 ≤ t → t ≤ T →
      condExp (E.fil (t - 1)) μ (fun ω => E.roundLoss c W pstar t ω + Ψ t ω - Ψ (t - 1) ω)
        ≤ᵐ[μ] fun ω => rho T t * Er t ω + C * m * W * rho T t)
    (hII : ∑ t ∈ Finset.Icc 2 T, rho T t * ∫ ω, Er t ω ∂μ ≤
      1 / 2 * ∫ ω, ∑ t ∈ Finset.Icc 1 T, E.roundLoss c W pstar t ω ∂μ
        + C * m * W * ∑ t ∈ Finset.Icc 2 T, rho T t)
    (hIII : ∫ ω, pstar ⬝ᵥ E.invAfter T ω - Ψ T ω ∂μ ≤ C * m * W * (1 + Real.log ((T : ℝ) + 1))) :
    E.expectedRegret c ≤ ENNReal.ofReal (12 * C * m * W * (1 + Real.log ((T : ℝ) + 1))) := by sorry

end UnobservedWelfare
