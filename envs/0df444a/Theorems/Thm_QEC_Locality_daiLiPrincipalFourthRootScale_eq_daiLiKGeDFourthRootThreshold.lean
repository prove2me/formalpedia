-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPrincipalFourthRootScale_eq_daiLiKGeDFourthRootThreshold
-- name    : QEC.Locality.daiLiPrincipalFourthRootScale_eq_daiLiKGeDFourthRootThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:38.487209+00:00
-- url     : https://prove2.me/theorems/5d4219a5-e34b-4892-9542-bf11b4870122
-- title:
--   Locality: dai Li Principal Fourth Root Scale eq dai Li KGe DFourth Root Threshold
-- statement:
--   The `rpow` scale used by the `d >= k` package agrees with the principal
--   square-root presentation used by the `k >= d` count theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/FinalComposition.lean#L46-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/FinalComposition.lean#L46-L56

import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.daiLiPrincipalFourthRootScale_eq_daiLiKGeDFourthRootThreshold
    (k d n : ℝ) (hk : 0 ≤ k) (hn : 0 < n) :
    daiLiPrincipalFourthRootScale k d n =
      daiLiKGeDFourthRootThreshold k d n := by sorry
