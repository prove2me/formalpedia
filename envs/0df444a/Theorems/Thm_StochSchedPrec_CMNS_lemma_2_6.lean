-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_lemma_2_6
-- name    : StochSchedPrec.CMNS.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:19.919974+00:00
-- url     : https://prove2.me/theorems/1c4d5eae-b940-4632-8d30-3a9e157b40ce
-- title:
--   Lemma 2.6, p. 795 — E[Σ_{i∈O_j(P)} P_i] = E[Σ_{i∈O_j(P)} E[P_i]]
-- statement:
--   Consider the standing stochastic model: $m\ge1$ machines, acyclic precedence constraints, release dates $r_j\ge0$ satisfying Assumption 2.1, and independent, nonnegative, integrable processing times $P_j$. Let $L$ be a linear extension of the precedence constraints, $\beta\ge0$, and let $\sigma$ be the CMNS policy with thresholds $\beta\,\mathrm E[P_j]$, nonanticipatory and measurable. For a job $j$ let $O_j(P)$ be the random set of jobs after $j$ in $L$ that are started before $j$. Then
--   $$\mathrm E\Big[\sum_{i\in O_j(P)}P_i\Big]=\mathrm E\Big[\sum_{i\in O_j(P)}\mathrm E[P_i]\Big].$$
--
--   The decision to start $i$ out of order is taken before $P_i$ is observed, so in expectation the out-of-order jobs contribute their expected processing times. This is where independence and nonanticipation enter the analysis.
--
--   **Formalization Note** Nonanticipation and measurability of the CMNS policy are taken as hypotheses: the paper asserts both for CMNS without proof (p. 795; §5, p. 800, where it requires universal measurability). The linear-extension hypothesis is the setting of Lemma 2.5 and Theorem 2.8; it is needed when processing times can be $0$ with positive probability: if a job $i\in A_j$ were a predecessor of $j$, then $P_i=0$ would let $j$ start at the same instant as $i$, so whether $i\in O_j(P)$ would depend on $P_i$.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 795, Lemma 2.6

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem lemma_2_6 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L) (β : ℝ) (hβ : 0 ≤ β)
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β (fun j => ∫ ω, P j ω ∂Pr) σ)
    (hσna : IsNonanticipatory σ)
    (hσm : AEMeasurable σ (Pr.map (fun ω k => P k ω))) (j : V) :
    ∫ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, P i ω ∂Pr
      = ∫ ω, ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, (∫ ω', P i ω' ∂Pr) ∂Pr := by sorry

end StochSchedPrec.CMNS
