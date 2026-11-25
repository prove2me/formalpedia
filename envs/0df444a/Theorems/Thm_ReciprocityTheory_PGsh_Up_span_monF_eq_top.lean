-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_span_monF_eq_top
-- name    : ReciprocityTheory.PGsh.Up.span_monF_eq_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:08:52.652939+00:00
-- url     : https://prove2.me/theorems/ffe3e462-8de2-4c4b-8fe8-42487c7719af
-- title:
--   Up: span mon F eq top
-- statement:
--   The Up construction uses the span mon F eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L195-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ProdEraseUpdate.lean#L195-L221

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]

theorem ReciprocityTheory.PGsh.Up.span_monF_eq_top (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) :
    Submodule.span k (Set.range (monF (p := p) Cm)) = ⊤ := by sorry
