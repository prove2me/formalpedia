-- Prove2me | Theorems.Thm_QEC_Locality_embedCoordinateVector_injective
-- name    : QEC.Locality.embedCoordinateVector_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:48.503856+00:00
-- url     : https://prove2.me/theorems/a94a6152-8f90-4dc4-b8f6-31658ee698ac
-- title:
--   Locality: embed Coordinate Vector injective
-- statement:
--   The Locality construction uses the embed Coordinate Vector injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L86-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L86-L97

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.embedCoordinateVector_injective (R : Finset ι) :
    Function.Injective (embedCoordinateVector R) := by sorry
