-- Prove2me | Theorems.Thm_QEC_Locality_restrictBinaryTo_eq_embeddedLocalPauli
-- name    : QEC.Locality.restrictBinaryTo_eq_embeddedLocalPauli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:02.013543+00:00
-- url     : https://prove2.me/theorems/f651c88b-6798-4ec6-9d7c-55da91eae300
-- title:
--   Locality: restrict Binary To eq embedded Local Pauli
-- statement:
--   The Locality construction uses the restrict Binary To eq embedded Local Pauli property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L35-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L35-L37

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.restrictBinaryTo_eq_embeddedLocalPauli (S : FiniteSubsystem ι) (E : Binary ι) :
    restrictBinaryTo S.selected E = embeddedLocalPauli S (localIndexOfBinary S E) := by sorry
