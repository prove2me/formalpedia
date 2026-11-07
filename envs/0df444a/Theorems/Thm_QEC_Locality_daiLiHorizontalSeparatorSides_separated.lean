-- Prove2me | Theorems.Thm_QEC_Locality_daiLiHorizontalSeparatorSides_separated
-- name    : QEC.Locality.daiLiHorizontalSeparatorSides_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:43.128517+00:00
-- url     : https://prove2.me/theorems/de851fdc-fcf7-49c6-b73c-b3540b29ad78
-- title:
--   Locality: dai Li Horizontal Separator Sides separated
-- statement:
--   The two exterior pieces constructed by actual horizontal cuts are at least
--   the cut width apart in the Euclidean embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1188-L1200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1188-L1200

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
omit [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.daiLiHorizontalSeparatorSides_separated
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut threshold : ℝ} (hWidth : threshold ≤ upperCut - lowerCut)
    {p q : ι}
    (hp : p ∈ daiLiHorizontalSeparatorLower embedding region lowerCut)
    (hq : q ∈ daiLiHorizontalSeparatorUpper embedding region upperCut) :
    threshold ≤ embedding.distance p q := by sorry
