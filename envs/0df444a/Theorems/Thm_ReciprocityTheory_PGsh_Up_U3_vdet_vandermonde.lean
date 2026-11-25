-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_vdet_vandermonde
-- name    : ReciprocityTheory.PGsh.Up.U3.vdet_vandermonde
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:47.738345+00:00
-- url     : https://prove2.me/theorems/0055c73d-1aa1-5580-b06d-4d13691c604e
-- title:
--   U3: vdet vandermonde
-- statement:
--   The U3 construction uses the vdet vandermonde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VdetLeOfSpanLe.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VdetLeOfSpanLe.lean#L78-L90

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

theorem ReciprocityTheory.PGsh.Up.U3.vdet_vandermonde [NeZero p] (ω : ZMod p → C)
    (hω : ∀ a b, a ≠ b → v (ω a - ω b) = 1) :
    v (Matrix.of fun a j : ZMod p => ω a ^ j.val).det = 1 := by sorry
