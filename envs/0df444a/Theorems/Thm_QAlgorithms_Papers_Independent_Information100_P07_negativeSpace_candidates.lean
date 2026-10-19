-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_negativeSpace_candidates
-- name    : QAlgorithms.Papers.Independent.Information100.P07.negativeSpace_candidates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:39:57.16285+00:00
-- url     : https://prove2.me/theorems/94caff17-d773-46d0-aa16-41173ffffaa0
-- title:
--   Unnumbered: four spectral candidates for NPT states
-- statement:
--   Let $\rho$ be an NPT two-qutrit state, $H_-=(\rho^\Gamma)_-$ its entire negative Jordan part, and
--   $$P_A=(P_{\operatorname{supp}\operatorname{Tr}_B H_-})^T,\qquad P_B=P_{\operatorname{supp}\operatorname{Tr}_A H_-}.$$
--   Its negative spectral range is a CES, and each local support has rank at least two and at most three. Every admissible rectangle $P\otimes Q$ contains these local supports. Consequently every admissible projector belongs to $\{P_A\otimes P_B,P_A\otimes I,I\otimes P_B,I\}$. The local supports computed using $H_-$ equal those computed using the projector onto the full negative spectral range.
--
--   This reduces admissible-rectangle search to at most four candidates, allowing repetitions. For every admissible R, the partial transpose of the exterior is positive and its support is orthogonal to that of the partial transpose of R rho R; their negative parts therefore satisfy (rho^Gamma)_- = ((R rho R)^Gamma)_-.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 3, Unnumbered: four spectral candidates for NPT states

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF pp.3,18: full negative subspace determines every admissible rectangle; its separable exterior is PPT and has orthogonal partial-transpose support. -/
theorem negativeSpace_candidates (rho : Joint) (hrho : IsDensityMatrix rho)
    (hnpt : ¬ (partialTransposeFirst rho).PosSemidef) :
    IsCES (operatorRange (negativePart (partialTransposeFirst rho))) ∧
    2 ≤ (negativeAlice rho).rank ∧ (negativeAlice rho).rank ≤ 3 ∧
    2 ≤ (negativeBob rho).rank ∧ (negativeBob rho).rank ≤ 3 ∧
    negativeAlice rho = (support (traceRight (negativeProjection (partialTransposeFirst rho)))).transpose ∧
    negativeBob rho = support (traceLeft (negativeProjection (partialTransposeFirst rho))) ∧
    (∀ P Q : Local, IsProjection P → IsProjection Q → Admissible rho (Matrix.kronecker P Q) →
      operatorRange (negativeAlice rho) ≤ operatorRange P ∧ operatorRange (negativeBob rho) ≤ operatorRange Q) ∧
    (∀ R, Admissible rho R → R = candidateZero rho ∨ R = candidateAlice rho ∨
      R = candidateBob rho ∨ R = 1) ∧
    (∀ R, Admissible rho R →
      (partialTransposeFirst (rho - R * rho * R)).PosSemidef ∧
      partialTransposeFirst (R * rho * R) * partialTransposeFirst (rho - R * rho * R) = 0 ∧
      negativePart (partialTransposeFirst rho) = negativePart (partialTransposeFirst (R * rho * R))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
