-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_nrm_rpow_neg_le_half
-- name    : ReciprocityTheory.Cheb.nrm_rpow_neg_le_half
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:45.129574+00:00
-- url     : https://prove2.me/theorems/cbd0a8e7-e1f1-4733-8a65-a10b2170259e
-- title:
--   Cheb: nrm rpow neg le half
-- statement:
--   The Cheb construction uses the nrm rpow neg le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeCont.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeCont.lean#L18-L24

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
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

theorem ReciprocityTheory.Cheb.nrm_rpow_neg_le_half {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 1 ≤ s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by sorry
