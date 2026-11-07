-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_site_add_range_le_end
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_site_add_range_le_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:52.20524+00:00
-- url     : https://prove2.me/theorems/20cb5f73-f62f-48ea-b245-231e5e31609b
-- title:
--   Strip Geometry: first Parity site add range le end
-- statement:
--   A first-parity strip always has a following second-parity strip, so its sites
--   remain one interaction range before the end of an even-width decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L490-L527
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L490-L527

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_site_add_range_le_end
    (L r start : Nat) (widths : List Nat)
    (hEven : Even widths.length)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width)
    {R : Finset (Site L)}
    (hR : R ∈ firstParity (openStripListAux L start widths))
    {p : Site L} (hp : p ∈ R) :
    p.1.val + r ≤ start + widths.sum := by sorry
