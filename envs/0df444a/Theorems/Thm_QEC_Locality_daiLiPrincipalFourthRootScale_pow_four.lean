-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPrincipalFourthRootScale_pow_four
-- name    : QEC.Locality.daiLiPrincipalFourthRootScale_pow_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:21.083027+00:00
-- url     : https://prove2.me/theorems/7919b46d-32a2-40c0-89c4-195379e702f5
-- title:
--   Locality: dai Li Principal Fourth Root Scale pow four
-- statement:
--   The principal fourth-root scale has the expected fourth power on its domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L205-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L205-L215

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

theorem QEC.Locality.daiLiPrincipalFourthRootScale_pow_four
    (k d n : ℝ) (hk : 0 ≤ k) (hn : 0 < n) :
    (daiLiPrincipalFourthRootScale k d n) ^ 4 =
      (1 / 100 : ℝ) ^ 4 * (k * d ^ 2 / n) := by sorry
