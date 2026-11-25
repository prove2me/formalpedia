-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_Nrm_rpow_neg_le_inv
-- name    : ReciprocityTheory.Cheb.Nrm_rpow_neg_le_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:14.091776+00:00
-- url     : https://prove2.me/theorems/248782e8-48c4-5684-85e4-c96d26345308
-- title:
--   Cheb: Nrm rpow neg le inv
-- statement:
--   The Cheb construction uses the Nrm rpow neg le inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeSum.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeSum.lean#L31-L35

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
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

theorem ReciprocityTheory.Cheb.Nrm_rpow_neg_le_inv {E : Type} [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) (q : Prm E) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by sorry
