-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiVerticalEqualBand_card_le
-- name    : QEC.Locality.exists_daiLiVerticalEqualBand_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:31.124355+00:00
-- url     : https://prove2.me/theorems/0364d7d6-6588-456a-8eda-f57bf5bd5d7d
-- title:
--   Locality: exists dai Li Vertical Equal Band card le
-- statement:
--   Finite pigeonhole for the actual equal-width bands.  The hypothesis is
--   the source average inequality, not a supplied low-count band: pairwise
--   disjointness and containment in `region` force one concrete band below it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L797-L835
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L797-L835

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

theorem QEC.Locality.exists_daiLiVerticalEqualBand_card_le
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper bound : ℝ} {m : Nat}
    (hM : 0 < m) (hSpan : 0 < upper - lower)
    (hAverage : (region.card : ℝ) ≤ m * bound) :
    ∃ i : Fin m,
      ((daiLiVerticalEqualBand embedding region lower upper m i).card : ℝ) ≤ bound := by sorry
