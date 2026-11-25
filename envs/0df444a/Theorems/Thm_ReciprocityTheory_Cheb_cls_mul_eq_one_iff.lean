-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cls_mul_eq_one_iff
-- name    : ReciprocityTheory.Cheb.cls_mul_eq_one_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:19.396364+00:00
-- url     : https://prove2.me/theorems/96e38f0c-fbea-4d59-8e4a-26529d9e8e23
-- title:
--   Cheb: cls mul eq one iff
-- statement:
--   The Cheb construction uses the cls mul eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/IdealLat.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/IdealLat.lean#L15-L22

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
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

theorem ReciprocityTheory.Cheb.cls_mul_eq_one_iff (a b : NZIdeal E) :
    cls a * cls b = 1 ↔ Submodule.IsPrincipal (a.1 * b.1) := by sorry
