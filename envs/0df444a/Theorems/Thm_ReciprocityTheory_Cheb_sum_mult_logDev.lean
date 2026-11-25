-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_sum_mult_logDev
-- name    : ReciprocityTheory.Cheb.sum_mult_logDev
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:14.42235+00:00
-- url     : https://prove2.me/theorems/cab76fa0-d97c-40a3-bdd9-9b5b777d69ff
-- title:
--   Cheb: sum mult log Dev
-- statement:
--   The Cheb construction uses the sum mult log Dev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/Support.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/Support.lean#L26-L41

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_Support
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.sum_mult_logDev {x : mixedSpace E} (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace E, (w.mult : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹) = 0 := by sorry
