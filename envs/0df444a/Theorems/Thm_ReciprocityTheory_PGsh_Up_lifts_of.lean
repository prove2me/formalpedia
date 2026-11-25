-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_lifts_of
-- name    : ReciprocityTheory.PGsh.Up.lifts_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:55.351131+00:00
-- url     : https://prove2.me/theorems/7a83f7a0-6655-506c-865c-96f586bdac2c
-- title:
--   Up: lifts of
-- statement:
--   The Up construction uses the lifts of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EqZeroOfIsoZero.lean#L46-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EqZeroOfIsoZero.lean#L46-L113

import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
import Definitions.Def_ReciprocityTheory_DualLattices_EqZeroOfIsoZero
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

theorem ReciprocityTheory.PGsh.Up.lifts_of (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement) :
    EigenLiftsStatement := by sorry
