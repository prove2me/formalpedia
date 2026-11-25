-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Loc_sep
-- name    : PI.LevelKSplit.W.Loc.sep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:51.440156+00:00
-- url     : https://prove2.me/theorems/f8b205b6-06c2-4117-a7df-a2650e39f968
-- title:
--   Loc: sep
-- statement:
--   The Loc construction uses the sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L60-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L60-L106

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}

theorem PI.LevelKSplit.W.Loc.sep (e f ce cf : Fin r → Fin n → B)
    (hee : ∀ a b, ce b ⬝ᵥ e a = 0)
    (hef : ∀ a b, ce b ⬝ᵥ f a = if a = b then 1 else 0)
    (hfe : ∀ a b, cf b ⬝ᵥ e a = if a = b then 1 else 0)
    (GX GW GY : Set (Fin n → B))
    (hGX : GX ⊆ span B (Set.range e)) (hGY : GY ⊆ span B (Set.range f))
    (hGW : ∀ w ∈ GW, ∀ b, ce b ⬝ᵥ w = 0 ∧ cf b ⬝ᵥ w = 0)
    (z y : Fin n → B) (hz : ∀ b, ce b ⬝ᵥ z = 0 ∧ cf b ⬝ᵥ z = 0)
    (hy : y ∈ span O (GX ∪ GW ∪ GY)) (hzy : z - y ∈ span B (Set.range e)) :
    z ∈ span O (GX ∪ GW ∪ GY) := by sorry
