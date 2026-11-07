-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_isStarProjection
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_isStarProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:17:42.21506+00:00
-- url     : https://prove2.me/theorems/a6ac940f-e8ca-4782-801c-1fa9be77b292
-- title:
--   Decoder Dressed Logical: good Syndrome Projector is Star Projection
-- statement:
--   The good-sector sum is a genuine self-adjoint projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L231-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L231-L235

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
open QEC.Coding.StabilizerCode.DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_isStarProjection
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    IsStarProjection (D.goodSyndromeProjector elementaryErrors) := by sorry
