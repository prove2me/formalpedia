-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_reps_X
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.UUA.reps_X
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:12.409309+00:00
-- url     : https://prove2.me/theorems/3b3bdcb6-aa21-4160-a5e1-8a6a71f6b90b
-- title:
--   UUA: reps X
-- statement:
--   The UUA construction uses the reps X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsCeil.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsCeil.lean#L7-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsCeil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA

theorem ReciprocityTheory.ChartRestriction.G.DVR.UUA.reps_X {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ) (hk : 1 ≤ k) :
    ∃ rep : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ χ : X, ∃ a μ, rep a + k • μ = χ) ∧
      (∀ a a' (μ μ' : X), rep a + k • μ = rep a' + k • μ' → a = a') ∧
      (∀ x y : X, k • x = k • y → x = y) := by sorry
