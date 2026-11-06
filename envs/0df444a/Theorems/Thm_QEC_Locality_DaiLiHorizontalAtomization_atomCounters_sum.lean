-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atomCounters_sum
-- name    : QEC.Locality.DaiLiHorizontalAtomization.atomCounters_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:51:18.99321+00:00
-- url     : https://prove2.me/theorems/dbe8da1c-5282-48d6-927f-206bd9f08644
-- title:
--   Dai Li Horizontal Atomization: atom Counters sum
-- statement:
--   The constructed geometric atomization preserves the actual Dai--Li counter
--   exactly.  This is the bridge from physical rectangles to the finite Nat greedy
--   kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L437-L471
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L437-L471

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.DaiLiHorizontalAtomization.atomCounters_sum
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hEll : 0 < ell) :
    (daiLiAtomCounters P embedding threshold left right atoms).sum =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle (left, lower) (right, upper)) := by sorry
