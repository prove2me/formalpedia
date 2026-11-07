-- Prove2me | Theorems.Thm_QEC_Locality_exceptionalBad_not_mem_daiLiDGeKBPrime
-- name    : QEC.Locality.exceptionalBad_not_mem_daiLiDGeKBPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:24.763263+00:00
-- url     : https://prove2.me/theorems/b5aec7a6-a086-43b3-9867-00240452ec8e
-- title:
--   Locality: exceptional Bad not mem dai Li DGe KBPrime
-- statement:
--   An exceptional bad qubit is genuinely outside `B'`: otherwise its own bad
--   incidence would have put it into the crossing-endpoint part of `C`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L320-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L320-L334

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK

theorem QEC.Locality.exceptionalBad_not_mem_daiLiDGeKBPrime
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (q : ι)
    (hq : q ∈ daiLiDGeKExceptionalBadQubits P embedding threshold w ell t) :
    q ∉ daiLiDGeKBPrimeQubits embedding w ell t := by sorry
