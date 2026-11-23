-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_summable_absNorm_rpow_ideal
-- name    : ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:33.465972+00:00
-- url     : https://prove2.me/theorems/6c76fbcc-b5e9-4484-af5a-e0076677dfcc
-- title:
--   Cheb: summable abs Norm rpow ideal
-- statement:
--   The Cheb construction uses the summable abs Norm rpow ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L81-L83

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

theorem ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) := by sorry
