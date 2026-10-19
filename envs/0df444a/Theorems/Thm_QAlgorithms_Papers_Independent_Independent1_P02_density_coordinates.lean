-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_density_coordinates
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.density_coordinates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:19:05.63799+00:00
-- url     : https://prove2.me/theorems/69d8e5c7-1dca-48a3-a23e-62660957041d
-- title:
--   Section 4, Eq.(23): density coordinates and purity bounds
-- statement:
--   Let $d\ge1$ and let $G_0,\ldots,G_{d^2-1}$ be a real Hilbert–Schmidt orthonormal basis of Hermitian matrices, with $G_0=I/\sqrt d$ and the remaining matrices traceless. For a density matrix $\rho$, put $w_j=\operatorname{Tr}(\rho G_j)$, which is real. Then
--
--   $$\rho=\sum_{j=0}^{d^2-1}w_jG_j=I/d+\sum_{j=1}^{d^2-1}w_jG_j,\qquad w_0=1/\sqrt d,$$
--
--   $$\sum_jw_j^2=\operatorname{Tr}(\rho^2)\le1,\qquad\sum_{j=1}^{d^2-1}w_j^2\le(d-1)/d.$$
--
--   The printed $w_0=\sqrt d$ is corrected to its reciprocal, as forced by trace normalization. This coordinate description is used in the map factorization; independent source moderation of the correction remains required.
--
--   **Correction to the printed source.**
--
--   Printed: The source prints w_0=d^(1/2) with G_0=d^(-1/2)I and trace rho=1.
--
--   Corrected: State w_0=d^(-1/2); all other displayed coefficient formulas are retained.
--
--   Reason: Directly Tr(rho G_0)=Tr(rho)/sqrt(d)=1/sqrt(d); rho=I/2 is a concrete counterexample to the printed exponent.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Section 4, Eq.(23): density coordinates and purity bounds, PDF p. 12. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

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


































































/-- Eq.(23), PDF p.12. Proposed correction w_0=d^(-1/2) replaces printed
d^(1/2), forced by trace one and G_0=I/sqrt(d). Pending independent moderation. -/
theorem density_coordinates (d : ℕ) (G : HermitianFrame d) (rho : Algebra d)
    (hDensity : IsDensityMatrix rho) :
    (∀ j, (rho*G.matrix j).trace = (hermitianCoordinates G rho j : ℂ)) ∧
    rho = ∑ j, (hermitianCoordinates G rho j : ℂ) • G.matrix j ∧
    rho = ((d : ℂ)⁻¹) • 1 + ∑ j ∈ Finset.univ.filter (fun j : Fin (d^2) => j.val ≠ 0),
      (hermitianCoordinates G rho j : ℂ) • G.matrix j ∧
    hermitianCoordinates G rho ⟨0,by have := G.positive; positivity⟩ = (Real.sqrt d)⁻¹ ∧
    (∑ j, (hermitianCoordinates G rho j)^2) = (rho*rho).trace.re ∧
    (rho*rho).trace.re ≤ 1 ∧
    (∑ j ∈ Finset.univ.filter (fun j : Fin (d^2) => j.val ≠ 0),
      (hermitianCoordinates G rho j)^2) ≤ ((d : ℝ)-1)/d := by sorry



end QAlgorithms.Papers.Independent.Independent1.P02
