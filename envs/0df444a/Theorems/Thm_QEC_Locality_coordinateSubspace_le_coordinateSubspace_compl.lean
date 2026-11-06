-- Prove2me | Theorems.Thm_QEC_Locality_coordinateSubspace_le_coordinateSubspace_compl
-- name    : QEC.Locality.coordinateSubspace_le_coordinateSubspace_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:07.464895+00:00
-- url     : https://prove2.me/theorems/bffc5cf3-1cd8-4504-97ae-1f6fd4ddb1c3
-- title:
--   Locality: coordinate Subspace le coordinate Subspace compl
-- statement:
--   A region disjoint from `R` lies in the coordinate complement of `R`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L143-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L143-L174

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

theorem QEC.Locality.coordinateSubspace_le_coordinateSubspace_compl
    {R T : Finset ι} (hDisjoint : Disjoint R T) :
    coordinateSubspace T ≤ coordinateSubspace Rᶜ := by sorry
