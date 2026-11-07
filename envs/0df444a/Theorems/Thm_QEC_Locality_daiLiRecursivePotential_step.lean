-- Prove2me | Theorems.Thm_QEC_Locality_daiLiRecursivePotential_step
-- name    : QEC.Locality.daiLiRecursivePotential_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:08:19.416014+00:00
-- url     : https://prove2.me/theorems/402511d4-d5cf-4369-ad66-63a7d566a55e
-- title:
--   Locality: dai Li Recursive Potential step
-- statement:
--   A `9/10`-balanced child gains at least the source strip charge in the
--   finite potential.  The rational estimate `sqrt(9/10) < 19/20` avoids any
--   unverified analytic approximation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1612-L1632
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1612-L1632

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

theorem QEC.Locality.daiLiRecursivePotential_step {ell : ℝ} {root parent child : Nat}
    (hEll : 0 ≤ ell) (hBalanced : 10 * child ≤ 9 * parent) :
    daiLiRecursivePotential ell root parent + 8 * ell * Real.sqrt parent ≤
      daiLiRecursivePotential ell root child := by sorry
