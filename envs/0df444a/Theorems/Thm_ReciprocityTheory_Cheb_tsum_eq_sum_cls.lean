-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_tsum_eq_sum_cls
-- name    : ReciprocityTheory.Cheb.tsum_eq_sum_cls
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:58.426424+00:00
-- url     : https://prove2.me/theorems/849be316-fe84-4cde-9c6f-cae5b8f8b341
-- title:
--   Cheb: tsum eq sum cls
-- statement:
--   The Cheb construction uses the tsum eq sum cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CTrick.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CTrick.lean#L44-L52

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_CTrick
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.tsum_eq_sum_cls (F : NZIdeal E → ℂ) (hF : Summable F) :
    ∑' a : NZIdeal E, F a = ∑ C : ClassGroup (𝓞 E), ∑' a : NZIdeal E, (if cls a = C then F a else 0) := by sorry
