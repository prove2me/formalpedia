-- Prove2me | Theorems.Thm_QEC_Locality_daiLiCorrectedFamilyCount_lt_budget_div
-- name    : QEC.Locality.daiLiCorrectedFamilyCount_lt_budget_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:53:40.681624+00:00
-- url     : https://prove2.me/theorems/be5f5160-b4d6-4982-bd1f-7a78b7cf98d8
-- title:
--   Locality: dai Li Corrected Family Count lt budget div
-- statement:
--   Arithmetic handoff for #386.  Under its still-required global incidence
--   budget `50 * totalF <= budget`, `d <= budget`, and the actual nonempty-bad
--   alternative, the corrected factor-30 subdivision count still gives the strict
--   rectangle budget `M < budget / d`.  The alternative is essential because Nat
--   division rounds down: either no rectangle was produced, or a bad square gives
--   `d <= 10 * totalF`.  For the Dai--Li application, `budget` is `max(k, d)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1602-L1615
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1602-L1615

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.daiLiCorrectedFamilyCount_lt_budget_div
    (M totalF d budget : Nat) (hD : 0 < d) (hDLeBudget : d ≤ budget)
    (hCount : M * d ≤ 30 * totalF) (hTotal : 50 * totalF ≤ budget)
    (hEmptyOrBad : M = 0 ∨ d ≤ 10 * totalF) :
    M < budget / d := by sorry
