-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_thetaQ_surj
-- name    : ReciprocityTheory.PGsh.Up.thetaQ_surj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:46:00.886018+00:00
-- url     : https://prove2.me/theorems/d88c31ad-2732-57eb-a3b6-4e6be518b683
-- title:
--   Up: theta Q surj
-- statement:
--   The Up construction uses the theta Q surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThetaQSurj.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThetaQSurj.lean#L79-L88

import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
import Definitions.Def_ReciprocityTheory_DualLattices_ThetaQSurj
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
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp}

theorem ReciprocityTheory.PGsh.Up.thetaQ_surj (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    Function.Surjective (thetaQ U τ) := by sorry
