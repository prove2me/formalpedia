-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_pa_Z_anti
-- name    : ReciprocityTheory.Cheb.pa_Z_anti
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:29.776901+00:00
-- url     : https://prove2.me/theorems/616ce0a1-c699-48b7-8870-ef15ea08d255
-- title:
--   Cheb: pa Z anti
-- statement:
--   The Cheb construction uses the pa Z anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/PrimeAsymp.lean#L116-L120

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
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

theorem ReciprocityTheory.Cheb.pa_Z_anti (E : Type) [Field E] [NumberField E] {s t : ℝ} (ht : 1 < t) (hts : t ≤ s) :
    ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t) := by sorry
