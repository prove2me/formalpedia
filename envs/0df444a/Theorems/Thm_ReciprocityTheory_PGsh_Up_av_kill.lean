-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_av_kill
-- name    : ReciprocityTheory.PGsh.Up.av_kill
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:08:06.907017+00:00
-- url     : https://prove2.me/theorems/bf8f7fc4-c2aa-401b-83b9-592e6f356dfa
-- title:
--   Up: av kill
-- statement:
--   The Up construction uses the av kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L121-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L121-L135

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

theorem ReciprocityTheory.PGsh.Up.av_kill (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) (a b : O) (hab : σ b = a) :
    ∀ m : htCoker H a b, cp • m = 0 := by sorry
