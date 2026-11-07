-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phase_eq_commutationPhase
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.phase_eq_commutationPhase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:17:08.307394+00:00
-- url     : https://prove2.me/theorems/3872e1c1-7a2f-41a5-971f-5b67f3bdb00c
-- title:
--   Decoder Dressed Logical: phase eq commutation Phase
-- statement:
--   The existing decoder phase is the symplectic commutation sign.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L69-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L69-L81

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.phase_eq_commutationPhase
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    D.phase logical syndrome =
      commutationPhase (D.correction syndrome) logical := by sorry
