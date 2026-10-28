-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_cq_qc_image_dimension
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.cq_qc_image_dimension
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:19:12.592491+00:00
-- url     : https://prove2.me/theorems/5ef8b4ba-cedf-496f-be7f-9e68c977d62a
-- title:
--   Section 4: rank and affine image dimension of CQ/QC
-- statement:
--   Let $d\ge1$, let $G$ be the Hermitian coordinate basis above, and let $\Phi$ be CQ or QC. Let $T$ be its full $d^2$-by-$d^2$ coordinate matrix and $\mathcal D_d$ the density matrices. Then
--
--   $$\operatorname{rank}T\le d,\qquad\dim_{\mathbb R}\operatorname{aff}(\Phi(\mathcal D_d))\le d-1.$$
--
--   The second dimension is affine in the trace-one hyperplane, following the separation of the identity coordinate on page 12. A linear-dimension interpretation would fail at $d=1$. This bounds the geometry of the output-state set.
--
--   **Correction to the printed source.**
--
--   Printed: The source calls the density image a subspace of dimension at most d-1.
--
--   Corrected: Interpret this as an affine span over the real numbers within the trace-one hyperplane.
--
--   Reason: Equation (23) fixes the identity coordinate; the convex hull of d density outputs has affine dimension at most d-1. Linear dimension zero already fails for the d=1 state.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Section 4: rank and affine image dimension of CQ/QC, PDF p. 13. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02




































































/-- Section 4, PDF p.13: full coordinate rank and affine dimension of density
outputs. "Subspace" is read as affine in the trace-one hyperplane, following
Eq.(23); a linear dimension d-1 claim fails already at d=1. -/
theorem cq_qc_image_dimension (d : ℕ) (G : HermitianFrame d) (Phi : Endomorphism d)
    (hClass : IsCQ Phi ∨ IsQC Phi) :
    (coordinateMatrix G Phi).rank ≤ d ∧
    Module.finrank ℝ (affineSpan ℝ (Phi '' {rho : Algebra d | IsDensityMatrix rho})).direction ≤ d-1 := by sorry

end QAlgorithms.Papers.Independent.Independent1.P02
