-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiTenthExterior_le_four_mul_tenth_pred
-- name    : QEC.Locality.card_daiLiTenthExterior_le_four_mul_tenth_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:06:56.489111+00:00
-- url     : https://prove2.me/theorems/8fb785ea-95d1-42c2-aa3c-1f5b78f9c65b
-- title:
--   Locality: card dai Li Tenth Exterior le four mul tenth pred
-- statement:
--   The four exterior tails together contain at most four times one less than
--   the exact tenth count.  Keeping this integer slack is essential for the
--   source's strict sixty-percent central-region estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L564-L612
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L564-L612

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
omit [Fintype ι]

theorem QEC.Locality.card_daiLiTenthExterior_le_four_mul_tenth_pred
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) :
    (daiLiTenthExterior embedding region hRegion).card ≤
      4 * (daiLiTenthCount region - 1) := by sorry
