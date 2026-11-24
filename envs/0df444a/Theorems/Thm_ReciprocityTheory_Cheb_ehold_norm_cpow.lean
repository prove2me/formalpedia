-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_ehold_norm_cpow
-- name    : ReciprocityTheory.Cheb.ehold_norm_cpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:17:14.123369+00:00
-- url     : https://prove2.me/theorems/fd84a2b5-1e48-493c-b017-a41e113cda0f
-- title:
--   Cheb: ehold norm cpow
-- statement:
--   The Cheb construction uses the ehold norm cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/ChebyshevLambdaSubPsiBounded.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/ChebyshevLambdaSubPsiBounded.lean#L12-L14

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
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

theorem ReciprocityTheory.Cheb.ehold_norm_cpow (n : ℕ) {s : ℝ} (hs : 1 < s) : ‖((n : ℂ) ^ (-(s : ℂ)))‖ = (n : ℝ) ^ (-s) := by sorry
