-- Prove2me | Theorems.Thm_QEC_Locality_commutes_of_disjoint_support
-- name    : QEC.Locality.commutes_of_disjoint_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:52.580327+00:00
-- url     : https://prove2.me/theorems/91486307-30da-4af9-83e1-8026b157b634
-- title:
--   Locality: commutes of disjoint support
-- statement:
--   Pauli representatives with disjoint physical supports commute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L93-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L93-L118

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

theorem QEC.Locality.commutes_of_disjoint_support (E F : Binary ι)
    (hdisjoint : Disjoint (support E) (support F)) : Commutes E F := by sorry
