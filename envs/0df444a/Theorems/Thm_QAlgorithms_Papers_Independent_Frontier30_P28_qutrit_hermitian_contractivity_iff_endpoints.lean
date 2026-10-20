-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_qutrit_hermitian_contractivity_iff_endpoints
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.qutrit_hermitian_contractivity_iff_endpoints
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:23:08.680865+00:00
-- url     : https://prove2.me/theorems/f6d3b57c-f109-40a4-95e9-4a002368503c
-- title:
--   Qutrit Hermitian contraction holds universally exactly at the endpoints
-- statement:
--   Fix $1\le p\le\infty$ and let $H_0=\{A\in M_3:A=A^*,\ \operatorname{tr}A=0\}$, with ordinary trace. Let induced norms be defined on the $H_0$ unit ball using Schatten norms and the spectral norm at infinity. Then
--
--   $$
--   \left[\ \|T|_{H_0}\|_{p-p}\le1\ \text{for every positive trace-preserving complex-linear }T:M_3\to M_3\ \right]
--   \iff p\in\{1,\infty\}.
--   $$
--
--   For each finite $1<p<\infty$, there are a completely positive trace-preserving map $T:M_3\to M_3$ and a traceless Hermitian matrix $A$ such that
--
--   $$
--   \|A\|_p=1,\qquad \|T(A)\|_p>1.
--   $$
--
--   This classifies universal Hermitian contractivity for qutrits; the intermediate-exponent failure is existential, so it is compatible with individual maps such as the identity being contractive.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 6, §III.B, first sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Unnumbered qutrit Hermitian classification, source PDF p.6, §III.B.
Universal contraction holds exactly at the endpoints. For intermediate finite
p, a CPTP map and a unit-norm traceless Hermitian expanding input exist;
it is not claimed that every qutrit map expands. -/
theorem qutrit_hermitian_contractivity_iff_endpoints
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ((∀ T : Lin 3 3, IsPositiveMap T → TracePreserving T →
      restrictedPNorm p T InHermitianTraceZero ≤ 1) ↔ p = 1 ∨ p = ⊤) ∧
    (1 < p → p < ⊤ → ∃ (T : Lin 3 3) (A : M 3),
      QAlgorithms.Entanglement.IsCompletelyPositive T ∧ TracePreserving T ∧
      InHermitianTraceZero A ∧ schattenNorm p A = 1 ∧
      1 < schattenNorm p (T A)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
