-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_site_lower
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_site_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:36:03.246711+00:00
-- url     : https://prove2.me/theorems/5a0f9c2c-3f36-4538-947a-dbd360a85604
-- title:
--   Strip Geometry: second Parity site lower
-- statement:
--   Every second-parity site lies after the first strip.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L530-L542
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L530-L542

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_site_lower
    {L start : Nat} {width₀ : Nat} {widths : List Nat}
    {R : Finset (Site L)}
    (hR :
      R ∈ secondParity
        (openStripListAux L start (width₀ :: widths)))
    {p : Site L} (hp : p ∈ R) :
    start + width₀ ≤ p.1.val := by sorry
