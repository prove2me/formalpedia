-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiDGeKSeparator_card_lt_k_of_principal_scale
-- name    : QEC.Locality.exists_daiLiDGeKSeparator_card_lt_k_of_principal_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:25.147541+00:00
-- url     : https://prove2.me/theorems/fddcc77e-ded9-4896-940d-cbfa8c510643
-- title:
--   Locality: exists dai Li DGe KSeparator card lt k of principal scale
-- statement:
--   The exact DL24 fourth-root substitution makes the Case-2 separator smaller
--   than `k`.  `d <= sqrt (k * n)` is the source's low-distance domain, written
--   with the principal nonnegative square root; `N` remains the actual unordered
--   long-interaction cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L1027-L1103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L1027-L1103

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

theorem QEC.Locality.exists_daiLiDGeKSeparator_card_lt_k_of_principal_scale
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell k d : ℝ)
    (hk : 0 < k) (hd : 0 < d) (_hDGeK : k ≤ d)
    (hn : 0 < (Fintype.card ι : ℝ))
    (hDistanceDomain : d ≤ Real.sqrt (k * Fintype.card ι))
    (hScale : ell = daiLiPrincipalFourthRootScale k d (Fintype.card ι))
    (hWidth : w = daiLiDGeKGridWidth d ell)
    (hLongCount : (P.longInteractionCount embedding threshold : ℝ) ≤ d / 100)
    (hGridScale : 4 * ell ≤ w) :
    ∃ t : GridTranslation w,
      ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) < k := by sorry
