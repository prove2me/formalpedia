-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P17_compression_sharp_invariant
-- name    : QAlgorithms.Papers.Independent.Intake100.P17.compression_sharp_invariant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:26:02.595146+00:00
-- url     : https://prove2.me/theorems/6a669012-7330-4314-b0a4-284ec5319a21
-- title:
--   Compression semigroup is sharp-invariant
-- statement:
--   Let \(G\) be a topological group with continuous involutive automorphism \(\tau\), acting continuously on a topological space \(X\). Let the homeomorphic involution \(r\) implement the action of \(\tau\), so \(r(grx)=\tau(g)x\). Suppose that \(D\subseteq X\) is open and \(r(D)=\operatorname{int}(X\setminus D)\). Define the compression set from this action by
--   \[
--   S_D=\{g\in G:gD\subseteq D\}.
--   \]
--   Then \(S_D\) is closed under multiplication and under \(g\mapsto g^\sharp=\tau(g)^{-1}\).
--
--   This supplies the involutive semigroup associated with a reflected domain. It asserts no kernel or Hilbert-space positivity.
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, PDF p. 9, Example 1.7(b): compression semigroup

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Example 1.7(b), PDF p. 9: the computed compression set is a semigroup stable
under sharp. Both sides of the complement/interior relation are retained. -/
theorem compression_sharp_invariant
    {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (tau : G ≃* G) (htau : Function.Involutive tau) (htaucont : Continuous tau)
    (r : X ≃ₜ X) (hr : Function.Involutive r)
    (hrcov : ∀ g x, r (g • r x) = tau g • x)
    (D : Set X) (hopen : IsOpen D) (hcomplement : r '' D = interior Dᶜ) :
    (∀ g ∈ compressionSet (G := G) D, ∀ h ∈ compressionSet (G := G) D,
      g * h ∈ compressionSet (G := G) D) ∧
    (∀ g ∈ compressionSet (G := G) D, (tau g)⁻¹ ∈ compressionSet (G := G) D) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P17

end
