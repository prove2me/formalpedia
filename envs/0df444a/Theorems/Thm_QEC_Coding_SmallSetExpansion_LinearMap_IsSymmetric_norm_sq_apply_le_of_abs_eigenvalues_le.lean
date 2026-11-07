-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_LinearMap_IsSymmetric_norm_sq_apply_le_of_abs_eigenvalues_le
-- name    : QEC.Coding.SmallSetExpansion.LinearMap.IsSymmetric.norm_sq_apply_le_of_abs_eigenvalues_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:37:42.167192+00:00
-- url     : https://prove2.me/theorems/f3ca6e7a-20c0-4117-a42f-23cf90b1249e
-- title:
--   Is Symmetric: norm sq apply le of abs eigenvalues le
-- statement:
--   A finite-dimensional self-adjoint operator whose eigenvalues all lie in
--   `[-spectral, spectral]` has the corresponding squared operator-norm bound.
--   This is the spectral-theorem step used after identifying Cayley adjacency
--   with a Hecke operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L23-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L23-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.LinearMap.IsSymmetric.norm_sq_apply_le_of_abs_eigenvalues_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {spectral : ℝ} (hSpectralNonnegative : 0 ≤ spectral)
    (hEigen : ∀ i : Fin (Module.finrank ℂ E),
      |hT.eigenvalues rfl i| ≤ spectral)
    (x : E) :
    ‖T x‖ ^ 2 ≤ spectral ^ 2 * ‖x‖ ^ 2 := by sorry
