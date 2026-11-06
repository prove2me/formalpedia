-- Prove2me | Theorems.Thm_QEC_Locality_support_restrictBinaryTo_subset
-- name    : QEC.Locality.support_restrictBinaryTo_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:12.477516+00:00
-- url     : https://prove2.me/theorems/4ff47227-b812-4a90-af1d-be35272347ef
-- title:
--   Locality: support restrict Binary To subset
-- statement:
--   The Locality construction uses the support restrict Binary To subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L39-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L39-L50

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

theorem QEC.Locality.support_restrictBinaryTo_subset (R : Finset ι) (E : Binary ι) :
    support (restrictBinaryTo R E) ⊆ R := by sorry
