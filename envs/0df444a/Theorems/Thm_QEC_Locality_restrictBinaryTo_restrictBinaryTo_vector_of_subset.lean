-- Prove2me | Theorems.Thm_QEC_Locality_restrictBinaryTo_restrictBinaryTo_vector_of_subset
-- name    : QEC.Locality.restrictBinaryTo_restrictBinaryTo_vector_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:00.104211+00:00
-- url     : https://prove2.me/theorems/b70d4983-f24a-447e-9e64-1c58b948fd57
-- title:
--   Locality: restrict Binary To restrict Binary To vector of subset
-- statement:
--   Restricting first to a smaller region and then to a larger one changes no vector data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L53-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L53-L73

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

theorem QEC.Locality.restrictBinaryTo_restrictBinaryTo_vector_of_subset
    (R S : Finset ι) (hRS : R ⊆ S) (E : Binary ι) :
    (restrictBinaryTo S (restrictBinaryTo R E)).vector = (restrictBinaryTo R E).vector := by sorry
