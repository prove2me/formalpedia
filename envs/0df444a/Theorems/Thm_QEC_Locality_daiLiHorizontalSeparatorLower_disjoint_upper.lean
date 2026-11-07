-- Prove2me | Theorems.Thm_QEC_Locality_daiLiHorizontalSeparatorLower_disjoint_upper
-- name    : QEC.Locality.daiLiHorizontalSeparatorLower_disjoint_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:40.022464+00:00
-- url     : https://prove2.me/theorems/235fa74e-0497-419b-b9a9-87aa92167b1b
-- title:
--   Locality: dai Li Horizontal Separator Lower disjoint upper
-- statement:
--   The two exterior sides are disjoint whenever the two selected lines are
--   ordered.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1159-L1168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1159-L1168

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

theorem QEC.Locality.daiLiHorizontalSeparatorLower_disjoint_upper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ} (hCuts : lowerCut ≤ upperCut) :
    Disjoint (daiLiHorizontalSeparatorLower embedding region lowerCut)
      (daiLiHorizontalSeparatorUpper embedding region upperCut) := by sorry
