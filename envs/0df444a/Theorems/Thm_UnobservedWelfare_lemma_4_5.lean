-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_4_5
-- name    : UnobservedWelfare.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:35.821963+00:00
-- url     : https://prove2.me/theorems/4309e34b-b36d-4691-8e9e-15df3f3aafa7
-- title:
--   Lemma 4.5 — conditional and cumulative drift (estimate (I))
-- statement:
--   Throughout, $c$ is an admissible cost, the buyer model on a standard Borel type space satisfies RC at scale $W>0$ and is centered ($S_\theta(1)=0$), $p^\star$ is a comparison price (34), $0<\gamma\le1$, $\kappa\ge80/\gamma$, $m,T\ge1$, and the execution (with any permitted demand selection) is of Algorithm 1.
--
--   Then $L_t,\Psi_t$ ($t\in[T]$) and $E_t$ ($2\le t\le T$) are integrable, and almost surely
--   $$\mathbb E[L_1+\Psi_1\mid\mathcal F_0]\le(\kappa+2)mW+2\varepsilon_T,$$
--   $$\mathbb E[L_t+\Psi_t-\Psi_{t-1}\mid\mathcal F_{t-1}]\le\rho_tE_t+(\kappa+1)mW\rho_t+2\varepsilon_T\qquad(2\le t\le T).$$
--   Consequently
--   $$\mathbb E\Big[\sum_{t=1}^TL_t+\Psi_T\Big]\le\sum_{t=2}^T\rho_t\mathbb E[E_t]+(\kappa+2)mW+(\kappa+1)mW\sum_{t=2}^T\rho_t+2T\varepsilon_T.$$
--
--   This is the potential-function step of the proof of Theorem 3.1 (estimate (I) of Lemma 3.2 with $C=\kappa+3$).
--
--   Differences from the source:
--   - generalization: the drift inequalities → the drift inequalities together with integrability of $L_t$, $\Psi_t$, $E_t$; reason: this integrability is the paper Lemma 4.4, which Lemma 4.5 relies on; dropping it gives the source statement
--   - encoding: conditional inequalities between random variables → `condExp` inequalities holding $\mu$-almost surely, $\mathcal F_t$ = `E.fil t`; reason: conditional expectations are defined up to null sets
--   - encoding: an execution of Algorithm 1 (well defined, measurable and safe by Lemmas 4.1, B.1 and 4.4) → an `Execution` (adapted processes with $q_t\in[0,1]^m$, $p_t\gg0$, $X_t\in D_{\theta_t}(p_t)$ on every path) driven by `alg1 m T W c γ κ`; reason: every execution of Algorithm 1 is such a record, by those lemmas; the records driven by `alg1` are exactly its executions
--   - encoding: rounds $t\in[T]$ → Lean round `k` is the paper round $t=k+1$; the analysis quantities take the paper index $t$; reason: index convention only
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 4.5, p.26 (PDF p.28); integrability from Lemma 4.4, p.25 (PDF p.27)

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

/-- **Lemma 4.5 (conditional and cumulative drift; estimate (I))** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 4.5, p.26 (PDF
p.28)). Under the standing assumptions of Sections 4–6 (p.22, p.27, p.32): an admissible cost `c`; an
i.i.d. buyer model on a standard Borel type space satisfying RC at scale `W > 0` and centered,
`S_θ(1) = 0` (p.18); a comparison price `p⋆` as in (34); `0 < γ ≤ 1` and `κ ≥ 80/γ`; and an
execution (every permitted demand selection) of Algorithm 1 with these `γ, κ`, the potential `Ψ_t` of (39) and the forgetting error `E_t` satisfy
`E[L_1 + Ψ_1 | F_0] ≤ (κ + 2)mW + 2ε_T` and
`E[L_t + Ψ_t − Ψ_{t−1} | F_{t−1}] ≤ ρ_t E_t + (κ + 1)mWρ_t + 2ε_T` for `2 ≤ t ≤ T`. Consequently
`E[Σ_{t=1}^T L_t + Ψ_T] ≤ Σ_{t=2}^T ρ_t E[E_t] + (κ + 2)mW + (κ + 1)mW Σ_{t=2}^T ρ_t + 2Tε_T`.

**Formalization Note** Rounds `t` are the paper's; `F_t` is `E.fil t`. The conditional
inequalities hold almost surely. The conclusion also records the integrability of `L_t`, `Ψ_t`
(`t ∈ [T]`) and `E_t` (`2 ≤ t ≤ T`), which the paper's Lemma 4.4 (p.25) supplies and without
which the conditional expectations would be the junk value `0`. -/
theorem lemma_4_5 {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) (W γ κ : ℝ) (hW : 0 < W) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 80 / γ ≤ κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0)
    (pstar : Fin m → ℝ) (hpstar : IsComparisonPrice u P c W T pstar)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Execution m T P u μ) (hE : E.DrivenBy (alg1 m T W c γ κ)) :
    (∀ t, 1 ≤ t → t ≤ T → Integrable (E.roundLoss c W pstar t) μ ∧ Integrable (E.potential W γ κ c pstar t) μ) ∧
    (∀ t, 2 ≤ t → t ≤ T → Integrable (E.forgettingError W γ κ c pstar t) μ) ∧
    (condExp (E.fil 0) μ (fun ω => E.roundLoss c W pstar 1 ω + E.potential W γ κ c pstar 1 ω)
      ≤ᵐ[μ] fun _ => (κ + 2) * m * W + 2 * epsT W T) ∧
    (∀ t, 2 ≤ t → t ≤ T →
      condExp (E.fil (t - 1)) μ (fun ω => E.roundLoss c W pstar t ω + E.potential W γ κ c pstar t ω - E.potential W γ κ c pstar (t - 1) ω)
        ≤ᵐ[μ] fun ω => rho T t * E.forgettingError W γ κ c pstar t ω + (κ + 1) * m * W * rho T t + 2 * epsT W T) ∧
    ∫ ω, (∑ t ∈ Finset.Icc 1 T, E.roundLoss c W pstar t ω) + E.potential W γ κ c pstar T ω ∂μ ≤
      ∑ t ∈ Finset.Icc 2 T, rho T t * ∫ ω, E.forgettingError W γ κ c pstar t ω ∂μ + (κ + 2) * m * W
        + (κ + 1) * m * W * ∑ t ∈ Finset.Icc 2 T, rho T t + 2 * T * epsT W T := by sorry

end UnobservedWelfare
