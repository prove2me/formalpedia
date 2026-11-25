-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_prj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Hf_prj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:39.622278+00:00
-- url     : https://prove2.me/theorems/586ee430-afb8-44dc-aebc-93b890c9c8da
-- title:
--   I2: Hf prj
-- statement:
--   The I2 construction uses the Hf prj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean#L95-L102

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Hf_prj {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {ξ : Vsp dim} (hξ : InPart σ ξ) (a : Vsp dim) :
    Hf ξ a = Hf ξ (prj σ a) := by sorry
