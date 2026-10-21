-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_common_dilation_continuity
-- name    : QAlgorithms.Papers.Independent.Support21.P17.common_dilation_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:53:56.843652+00:00
-- url     : https://prove2.me/theorems/b0007edd-5fba-4755-a7bd-1d9d3a3cec64
-- title:
--   Finite-dimensional common dilation continuity
-- statement:
--   Let $m,n>0$ and let $T_1,T_2:M_m\to M_n$ be CP maps, with no unitality or subunitality assumption. There are common dilation operators $V_i:\mathbb C^n\to\mathbb C^m\otimes(\mathbb C^n\otimes\mathbb C^m)$ such that $T_i(A)=V_i^*(A\otimes I)V_i$ and
--
--   $$\|V_1-V_2\|\le m\sqrt{\|T_1-T_2\|_{\rm cb}}.$$
--
--   The stated common environment is the one explicitly constructed in the proof and need not be minimal. This is an existence estimate; the factor $m=\dim H$ lies outside the square root.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 18, Lemma 6.1: finite-dimensional common dilation continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Lemma 6.1, PDF pp.18–19: finite-dimensional CP maps admit common, generally
nonminimal, dilations with distance at most dim(H) times the square root of the CB
distance. The proof's explicit common environment is K tensor H. -/
theorem common_dilation_continuity (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (T1 T2 : Lin m n) (hT1 : Entanglement.IsCompletelyPositive T1)
    (hT2 : Entanglement.IsCompletelyPositive T2) :
    ∃ V1 V2 : Matrix (Fin m × (Fin n × Fin m)) (Fin n) ℂ,
      (∀ A, T1 A = V1.conjTranspose * Matrix.kronecker A
        (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) * V1) ∧
      (∀ A, T2 A = V2.conjTranspose * Matrix.kronecker A
        (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) * V2) ∧
      specNorm (V1 - V2) ≤ (m : ℝ) * Real.sqrt (matrixCBNorm (T1 - T2)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
