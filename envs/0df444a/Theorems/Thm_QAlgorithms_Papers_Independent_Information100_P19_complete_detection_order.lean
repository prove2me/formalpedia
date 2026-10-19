-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_complete_detection_order
-- name    : QAlgorithms.Papers.Independent.Information100.P19.complete_detection_order
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:03:58.449871+00:00
-- url     : https://prove2.me/theorems/2e413255-e27b-44d3-a8aa-a3ea32496668
-- title:
--   Theorem 6.5
-- statement:
--   Let $V_P,V_E,V_M,V_S$ be the strict-negative detection sets for the three-moment PPT, centered one-moment, second binomial, and pair-sum defects, respectively. Each set ranges over the disjoint union of all positive finite local dimensions and all density matrices. The complete ordering is
--   $$V_M\subsetneq V_P,\qquad V_M\subsetneq V_S.$$
--   Every other ordered inclusion between distinct sets fails. Non-inclusion asserts a witness in some finite dimensions, rather than in every fixed dimension pair.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 42, Theorem 6.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Theorem 6.5; arXiv:2609.29471v1, PDF pp.42, 43, 44. -/
theorem complete_detection_order  :
    detection 2 ⊂ detection 0 ∧ detection 2 ⊂ detection 3 ∧
    ∀ i j : Fin 4, i≠j →
      ((detection i ⊆ detection j) ↔ i=2 ∧ (j=0 ∨ j=3)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
