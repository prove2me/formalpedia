-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_vdet_pow
-- name    : ReciprocityTheory.PGsh.Up.U3.vdet_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:14.239675+00:00
-- url     : https://prove2.me/theorems/d243c371-a743-4d89-8efb-9290051ff695
-- title:
--   U3: vdet pow
-- statement:
--   The U3 construction uses the vdet pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VdetLeOfSpanLe.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VdetLeOfSpanLe.lean#L92-L100

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {p : ℕ} [hp : Fact p.Prime]

theorem ReciprocityTheory.PGsh.Up.U3.vdet_pow [NeZero p] (ω : ZMod p → C) (hω : ∀ a b, a ≠ b → v (ω a - ω b) = 1) (c : C) :
    v (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val).det = v c ^ (p * (p - 1) / 2) := by sorry
