-- Prove2me | Theorems.Thm_StochSchedPrec_InForest_lemma_4_4
-- name    : StochSchedPrec.InForest.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:28.208542+00:00
-- url     : https://prove2.me/theorems/6a25eab1-8cb3-46d4-85a0-d8693ee12507
-- title:
--   Lemma 4.4, p. 800 — E[C_j(P)] ≤ (m−1)/m E[ℓ_j(P)] + 1/m Σ_{B_j} E[P_i] under Graham's list scheduling
-- statement:
--   Consider the stochastic scheduling problem with an acyclic in-forest of precedence constraints on $V$, $m\ge 1$ identical machines, no release dates, and independent, nonnegative, integrable processing times $P_j$. Let $L$ be a priority list that is a linear extension of the precedence constraints, and let $\gamma$ be Graham's list scheduling with list $L$: for every realization $p\ge 0$, $\gamma(p)$ is the Graham schedule. Fix for every realization a selector of critical predecessors, and let $\ell_j(P)$ be the length of the critical chain for $j$. Then for every job $j$, the completion time $C_j(P)=S^\gamma_j(P)+P_j$ satisfies
--   $$\mathrm E[C_j(P)]\ \le\ \frac{m-1}{m}\,\mathrm E[\ell_j(P)]+\frac1m\sum_{i\in B_j}\mathrm E[P_i]. \tag{4.1}$$
--
--   Combined with the LP bound of Lemma 3.3 and the critical-chain lower bound, this gives the performance guarantee of Theorem 4.5.
--
--   **Formalization Note** The page presupposes that $C_j(P)$ and $\ell_j(P)$ are random variables (§5, p. 800, asserts measurability of the paper's policies without proof); this is taken as the hypothesis that both are almost-everywhere measurable. Integrability of the $P_j$ is assumed so that the expectations on the right are finite.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 800, Lemma 4.4, (4.1); measurability: §5, p. 800

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
import Definitions.Def_StochSchedPrec_InForest_Graham
open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.InForest

theorem lemma_4_4 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A) (hforest : IsInForest A)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (hPint : ∀ j, Integrable (P j) Pr)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsLinearExtension A L)
    (γ : (V → ℝ) → (V → ℝ)) (hγ : ∀ p, IsNonneg p → IsGraham A m L p (γ p))
    (hγmeas : ∀ j, AEMeasurable (fun ω => γ (fun k => P k ω) j) Pr)
    (crit : (V → ℝ) → V → Option V) (hcrit : ∀ p, IsNonneg p → IsCritSelector A p (γ p) (crit p))
    (hℓmeas : ∀ j, AEMeasurable
      (fun ω => chainLen (crit (fun k => P k ω)) (fun k => P k ω) j) Pr)
    (j : V) :
    ∫ ω, (γ (fun k => P k ω) j + P j ω) ∂Pr ≤
      ((m : ℝ) - 1) / m * ∫ ω, chainLen (crit (fun k => P k ω)) (fun k => P k ω) j ∂Pr
        + 1 / (m : ℝ) * ∑ i ∈ Bset L j, ∫ ω, P i ω ∂Pr := by sorry

end StochSchedPrec.InForest
