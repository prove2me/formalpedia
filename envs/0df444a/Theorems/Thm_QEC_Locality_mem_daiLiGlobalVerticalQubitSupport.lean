-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiGlobalVerticalQubitSupport
-- name    : QEC.Locality.mem_daiLiGlobalVerticalQubitSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:47:10.164347+00:00
-- url     : https://prove2.me/theorems/ee2303ae-1787-48dc-9108-99d5f5f104b3
-- title:
--   Locality: mem dai Li Global Vertical Qubit Support
-- statement:
--   The Locality construction uses the mem dai Li Global Vertical Qubit Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L32-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L32-L35

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.mem_daiLiGlobalVerticalQubitSupport
    (embedding : UnitSeparatedEmbedding2D ι) (q : ι) :
    (embedding.point q).2 ∈ daiLiGlobalVerticalQubitSupport embedding := by sorry
