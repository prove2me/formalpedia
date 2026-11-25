-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_emb_dual
-- name    : ReciprocityTheory.ChartRestriction.G.I2.emb_dual
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:29:01.58501+00:00
-- url     : https://prove2.me/theorems/04885c2c-11b5-4a01-b74c-81a4673b3cd3
-- title:
--   I2: emb dual
-- statement:
--   The I2 construction uses the emb dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVB.lean#L73-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVB.lean#L73-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB
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
variable {dim : (E →+* ℂ) → ℕ}

theorem ReciprocityTheory.ChartRestriction.G.I2.emb_dual (x ξ : Vsp dim) (y : E)
    (hy : ∀ β : 𝓞 E, ((Algebra.trace ℚ E ((β : E) * y) : ℚ) : ℝ) = (Hf x (act β ξ)).im) (σ : E →+* ℂ) :
    σ y = (hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I) := by sorry
