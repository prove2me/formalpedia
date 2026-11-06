-- Prove2me | Theorems.Thm_QEC_Locality_coordinateSubspace_compl_le_orthogonal
-- name    : QEC.Locality.coordinateSubspace_compl_le_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:42.327395+00:00
-- url     : https://prove2.me/theorems/33ea6042-c4e6-4d99-97d0-0b17ecf67fa2
-- title:
--   Locality: coordinate Subspace compl le orthogonal
-- statement:
--   Coordinates outside a region symplectically commute with every coordinate in it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L110-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/TwoCorrectableRegionsDimension.lean#L110-L121

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

theorem QEC.Locality.coordinateSubspace_compl_le_orthogonal (R : Finset ι) :
    coordinateSubspace Rᶜ ≤
      FiniteSymplectic.form.orthogonal (coordinateSubspace R) := by sorry
