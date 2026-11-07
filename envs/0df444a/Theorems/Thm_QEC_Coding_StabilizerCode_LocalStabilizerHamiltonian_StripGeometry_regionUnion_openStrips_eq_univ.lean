-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_regionUnion_openStrips_eq_univ
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.regionUnion_openStrips_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:34:22.062393+00:00
-- url     : https://prove2.me/theorems/c04596fc-9526-4e38-a981-8ef077071e79
-- title:
--   Strip Geometry: region Union open Strips eq univ
-- statement:
--   A width decomposition summing to `L` covers the full square lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L718-L724
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L718-L724

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.regionUnion_openStrips_eq_univ
    {L r : Nat} (D : AlternatingWidthDecomposition L r) :
    regionUnion (openStripListAux L 0 D.widths) =
      (Finset.univ : Finset (Site L)) := by sorry
