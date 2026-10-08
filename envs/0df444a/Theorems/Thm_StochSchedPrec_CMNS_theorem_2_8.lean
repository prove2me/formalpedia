-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_theorem_2_8
-- name    : StochSchedPrec.CMNS.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:21.685834+00:00
-- url     : https://prove2.me/theorems/351c57d0-dccb-486e-8d80-d8ce5154ad6e
-- title:
--   Theorem 2.8, p. 796 — expected completion-time bound (2.5) for Algorithm CMNS
-- statement:
--   Consider an instance of $\mathrm P\,|\,r_j,\mathit{prec}\,|\,\gamma$ in the standing stochastic model, with Assumption 2.1, a priority list $L$ that is a linear extension of the precedence constraints, $\beta>0$, and the CMNS policy $\sigma$ with thresholds $\beta\,\mathrm E[P_j]$ (nonanticipatory and measurable). Then the completion time $C_j(P)$ of every job $j$ is integrable and
--   $$\mathrm E[C_j(P)]\le\Big(\frac{m-1}m+\frac1\beta\Big)\mathrm E[\ell_j(P)]+\frac{1+\beta}m\sum_{i\in B_j}\mathrm E[P_i]+\frac1m\,r_j,$$
--   where $\ell_j(P)$ is the length of the critical chain of $j$ in $\sigma(P)$ and $B_j$ the set of jobs up to and including $j$ in $L$.
--
--   This is the upper-bound half of the approximation guarantee of Theorem 4.1; no assumption on the distributions beyond independence and finite means is needed.
--
--   **Formalization Note** The page writes $\beta\ge0$; at $\beta=0$ the bound is vacuous on the page ($1/\beta=+\infty$) but would be false in Lean ($1/0=0$), so $\beta>0$ is assumed. Integrability of $C_j(P)$ is part of the conclusion. Nonanticipation and measurability of the CMNS policy are the paper's assertions (p. 795; §5, p. 800), taken as hypotheses.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 796, Theorem 2.8, eq. (2.5)

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem theorem_2_8 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L) (β : ℝ) (hβ : 0 < β)
    (tb : V ≃ Fin (Fintype.card V))
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β (fun j => ∫ ω, P j ω ∂Pr) σ)
    (hσna : IsNonanticipatory σ)
    (hσm : AEMeasurable σ (Pr.map (fun ω k => P k ω))) (j : V) :
    Integrable (fun ω => σ (fun k => P k ω) j + P j ω) Pr ∧
    ∫ ω, (σ (fun k => P k ω) j + P j ω) ∂Pr
      ≤ (((m : ℝ) - 1) / m + 1 / β)
          * ∫ ω, chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j ∂Pr
        + (1 + β) / m * ∑ i ∈ before L j, ∫ ω, P i ω ∂Pr + 1 / (m : ℝ) * r j := by sorry

end StochSchedPrec.CMNS
