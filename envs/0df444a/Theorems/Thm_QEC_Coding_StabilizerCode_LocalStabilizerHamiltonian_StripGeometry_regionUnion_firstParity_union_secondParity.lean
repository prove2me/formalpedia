-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_regionUnion_firstParity_union_secondParity
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.regionUnion_firstParity_union_secondParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:34:33.932221+00:00
-- url     : https://prove2.me/theorems/1f1ed296-da63-48fe-bd22-6b6b183a53eb
-- title:
--   Strip Geometry: region Union first Parity union second Parity
-- statement:
--   The two parity sublists together have the same union as the full list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L759-L777
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L759-L777

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.regionUnion_firstParity_union_secondParity
    {α : Type*} [DecidableEq α] (regions : List (Finset α)) :
    regionUnion (firstParity regions) ∪
        regionUnion (secondParity regions) =
      regionUnion regions := by sorry
