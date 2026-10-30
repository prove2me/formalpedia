-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_reference_support_dimension
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.reference_support_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:57:49.789635+00:00
-- url     : https://prove2.me/theorems/578f8c26-33ce-4e8e-a30d-7fa5a8076b5f
-- title:
--   Polynomial bound on the reference vector-orbit support dimension
-- statement:
--   Let $d\ge2$ and $r\ge1$, so the reference register contains $n_R=2r$ physical $d$-level systems. Let $|\psi\rangle$ be a normalized vector on $(\mathbb C^d)^{\otimes r}\otimes(\mathbb C^d)^{\otimes r}$. Define its orbit support
--
--   $$K_\psi=\operatorname{span}\{(U^{\otimes r}\otimes I)|\psi\rangle:U\in\mathrm{SU}(d)\}.$$
--
--   Then
--
--   $$\dim K_\psi\le(r+1)^{d^2-1}.$$
--
--   In particular this applies to the paper's reference states and repeated-block preparations, after the fixed wire regrouping. This support bound permits exact compression into a polynomial-dimensional Hilbert space.
--
--   **Formalization Note** This follows D2--D3's vector-support/rank argument. The printed D1 instead writes a span of density operators, whose dimension can differ; that source discrepancy requires independent moderation.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 29, D2--D3; corrected support interpretation of D1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Effective support dimension, Eq.(15) and D3, PDF pp.7,29. Here nR=2r.
The proof's representation bound is independent of the chosen normalized seed, and
therefore in particular applies to A9 and to all repeated-block reference states.
SOURCE CORRECTION: support dimension, not the operator-orbit span printed in D1. -/
theorem reference_support_dimension (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (psi : EuclideanSpace ℂ ((Register (fun _ : Fin r => d)) × (Register (fun _ : Fin r => d)))) (hpsi : ‖psi‖ = 1) :
    Module.finrank ℂ (referenceOrbitSpan psi) ≤ (r + 1) ^ (d ^ 2 - 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
