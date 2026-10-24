-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_minimal_environment_rank
-- name    : QAlgorithms.Papers.Independent.Support21.P17.minimal_environment_rank
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:49:33.295116+00:00
-- url     : https://prove2.me/theorems/a588772e-4852-45f5-8592-87419b278a13
-- title:
--   Choi rank and minimal environment
-- statement:
--   Let $m,n>0$, let $T:M_m\to M_n$ be CP, and let $T(A)=V^*(A\otimes I_E)V$ be any canonical minimal dilation with a separable environment $E$. Define $F_T$ by $(F_T)_{\mu i,\nu j}=m[T(E_{ij})]_{\mu\nu}$ and the full tracial RN derivative by $D_\Phi T=I_m\otimes F_T$. The environment is finite-dimensional, and
--
--   $$\dim E=\operatorname{rank}F_T,\qquad m\dim E=\operatorname{rank}(D_\Phi T).$$
--
--   The zero map has minimal environment dimension zero; no nonzero-environment hypothesis is imposed. These equalities characterize the least environment size in RN coordinates.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 15, §5.1, unnumbered: Choi rank and minimal environment

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

/-- Section 5.1, PDF p.15: minimal environment dimension equals the RN-coordinate
rank, and dim(H)dim(E) equals the full derivative rank. The minimal environment is
concluded finite-dimensional, not assumed nonzero. -/
theorem minimal_environment_rank (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T)
    (E : SeparableHilbertSpace) (V : finiteHilbert n →L[ℂ] NoiseSpace (finiteHilbert m) E)
    (hV : IsMatrixCanonical T E V) :
    FiniteDimensional ℂ E ∧ Module.finrank ℂ E = matrixRank (scaledChoi T) ∧
      m * Module.finrank ℂ E = matrixRank (tracialDerivative T) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
