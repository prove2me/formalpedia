-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_lemma_2_7
-- name    : StochSchedPrec.CMNS.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:29.912414+00:00
-- url     : https://prove2.me/theorems/14cfa8f5-906e-40f9-8970-16559912ad08
-- title:
--   Lemma 2.7, p. 795 — (1/m) E[Σ_{i∈O_j(P)} E[P_i]] ≤ (1/β) E[ℓ_j(P)]
-- statement:
--   In the standing stochastic model (with Assumption 2.1), let $L$ be a linear extension of the precedence constraints, $\beta>0$, and $\sigma$ a measurable CMNS policy with thresholds $\beta\,\mathrm E[P_j]$. For a job $j$ let $O_j(P)$ be the random set of jobs after $j$ in $L$ started before $j$, and $\ell_j(P)$ the length of the critical chain of $j$ in the schedule $\sigma(P)$ (for a fixed tie-breaking rule). Then
--   $$\frac1m\,\mathrm E\Big[\sum_{i\in O_j(P)}\mathrm E[P_i]\Big]\le\frac1\beta\,\mathrm E[\ell_j(P)].$$
--
--   Each out-of-order job has been charged its full threshold $\beta\mathrm E[P_i]$ before $j$ starts, and that charge fits in the parts of $[0,S_j(P)[$ not covered by the critical chain's waiting intervals.
--
--   **Formalization Note** The paper allows $\beta\ge0$ in this section; at $\beta=0$ the right-hand side is $+\infty$ on the page but $0$ in Lean ($1/0=0$), so the statement requires $\beta>0$. Measurability of the policy is the paper's §5 assumption.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 795, Lemma 2.7

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem lemma_2_7 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L) (β : ℝ) (hβ : 0 < β)
    (tb : V ≃ Fin (Fintype.card V))
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β (fun j => ∫ ω, P j ω ∂Pr) σ)
    (hσm : AEMeasurable (fun ω => σ (fun k => P k ω)) Pr) (j : V) :
    1 / (m : ℝ) * ∫ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, (∫ ω', P i ω' ∂Pr) ∂Pr
      ≤ 1 / β * ∫ ω, chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j ∂Pr := by sorry

end StochSchedPrec.CMNS
