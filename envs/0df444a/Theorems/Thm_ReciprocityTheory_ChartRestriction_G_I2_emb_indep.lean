-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_emb_indep
-- name    : ReciprocityTheory.ChartRestriction.G.I2.emb_indep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:33.43292+00:00
-- url     : https://prove2.me/theorems/abb90a1a-ab59-47ca-a4d8-2575cb255d4e
-- title:
--   I2: emb indep
-- statement:
--   The I2 construction uses the emb indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean#L11-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.emb_indep (g : (E →+* ℂ) → ℂ) (h : ∀ β : 𝓞 E, ∑ σ, σ (β : E) * g σ = 0) : g = 0 := by sorry
