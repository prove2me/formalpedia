-- Prove2me | Theorems.Thm_QEC_Locality_symplecticForm_add_left
-- name    : QEC.Locality.symplecticForm_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:38.788354+00:00
-- url     : https://prove2.me/theorems/ba8212de-73ba-4078-8789-ecb7d6b3f398
-- title:
--   Locality: symplectic Form add left
-- statement:
--   The Locality construction uses the symplectic Form add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L181-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L181-L188

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

theorem QEC.Locality.symplecticForm_add_left (a b c : SymplecticVector (ZMod 2) ι) :
    symplecticForm (a + b) c = symplecticForm a c + symplecticForm b c := by sorry
