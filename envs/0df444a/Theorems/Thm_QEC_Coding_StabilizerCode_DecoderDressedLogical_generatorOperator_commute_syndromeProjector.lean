-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_generatorOperator_commute_syndromeProjector
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.generatorOperator_commute_syndromeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:15:41.164306+00:00
-- url     : https://prove2.me/theorems/966d2340-d2be-424a-b743-e7200d4f2404
-- title:
--   Decoder Dressed Logical: generator Operator commute syndrome Projector
-- statement:
--   Every selected generator preserves every syndrome sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L566-L590
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L566-L590

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.generatorOperator_commute_syndromeProjector
    (_D : DecoderDressedLogical H) (check : κ)
    (syndrome : DecoderSyndrome κ) :
    Commute (H.generatorOperator check) (H.syndromeProjector syndrome) := by sorry
