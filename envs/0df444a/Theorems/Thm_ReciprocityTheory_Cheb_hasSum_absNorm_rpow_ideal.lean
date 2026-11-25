-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_hasSum_absNorm_rpow_ideal
-- name    : ReciprocityTheory.Cheb.hasSum_absNorm_rpow_ideal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:55.494155+00:00
-- url     : https://prove2.me/theorems/43d53972-da96-470c-8d0a-9ff8a23f140c
-- title:
--   Cheb: has Sum abs Norm rpow ideal
-- statement:
--   The Cheb construction uses the has Sum abs Norm rpow ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L85-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L85-L104

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.hasSum_absNorm_rpow_ideal (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    HasSum (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) (idealZetaR E s) := by sorry
