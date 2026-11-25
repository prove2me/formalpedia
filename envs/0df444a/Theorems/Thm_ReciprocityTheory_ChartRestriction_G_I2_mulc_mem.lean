-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_mulc_mem
-- name    : ReciprocityTheory.ChartRestriction.G.I2.mulc_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:27.952806+00:00
-- url     : https://prove2.me/theorems/8c9a6505-0412-4fd0-9787-f254d2329f8a
-- title:
--   I2: mulc mem
-- statement:
--   The I2 construction uses the mulc mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean#L32-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean#L32-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.mulc_mem {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim))
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) :
    ∀ v ∈ Submodule.span ℂ (I : Set (Vsp dim)), prj σ v ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by sorry
