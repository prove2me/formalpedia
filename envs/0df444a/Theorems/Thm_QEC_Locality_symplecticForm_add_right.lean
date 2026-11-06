-- Prove2me | Theorems.Thm_QEC_Locality_symplecticForm_add_right
-- name    : QEC.Locality.symplecticForm_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:23.546007+00:00
-- url     : https://prove2.me/theorems/428e82ef-9b11-47d6-83e4-316f600bf4e5
-- title:
--   Locality: symplectic Form add right
-- statement:
--   The Locality construction uses the symplectic Form add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L191-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L191-L195

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
omit [DecidableEq ι]

theorem QEC.Locality.symplecticForm_add_right (a b c : SymplecticVector (ZMod 2) ι) :
    symplecticForm a (b + c) = symplecticForm a b + symplecticForm a c := by sorry
