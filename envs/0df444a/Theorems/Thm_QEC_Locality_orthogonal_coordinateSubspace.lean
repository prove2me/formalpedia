-- Prove2me | Theorems.Thm_QEC_Locality_orthogonal_coordinateSubspace
-- name    : QEC.Locality.orthogonal_coordinateSubspace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:03.962203+00:00
-- url     : https://prove2.me/theorems/4b7f765f-f6b0-42ed-a2be-fbb71dd40acf
-- title:
--   Locality: orthogonal coordinate Subspace
-- statement:
--   The symplectic orthogonal of a coordinate region is its finite complement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L133-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L133-L140

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

theorem QEC.Locality.orthogonal_coordinateSubspace (R : Finset ι) :
    FiniteSymplectic.form.orthogonal (coordinateSubspace R) = coordinateSubspace Rᶜ := by sorry
