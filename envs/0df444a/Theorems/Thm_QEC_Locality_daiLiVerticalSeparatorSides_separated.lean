-- Prove2me | Theorems.Thm_QEC_Locality_daiLiVerticalSeparatorSides_separated
-- name    : QEC.Locality.daiLiVerticalSeparatorSides_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:53.741241+00:00
-- url     : https://prove2.me/theorems/62e8043c-7210-41fb-beb7-dba6bf079f06
-- title:
--   Locality: dai Li Vertical Separator Sides separated
-- statement:
--   Opposite vertical sides are separated in the actual Euclidean embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1307-L1330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1307-L1330

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

theorem QEC.Locality.daiLiVerticalSeparatorSides_separated
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut threshold : ℝ} (hWidth : threshold ≤ upperCut - lowerCut)
    {p q : ι}
    (hp : p ∈ daiLiVerticalSeparatorLower embedding region lowerCut)
    (hq : q ∈ daiLiVerticalSeparatorUpper embedding region upperCut) :
    threshold ≤ embedding.distance p q := by sorry
