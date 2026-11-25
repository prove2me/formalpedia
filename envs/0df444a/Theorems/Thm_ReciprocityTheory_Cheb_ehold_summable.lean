-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_ehold_summable
-- name    : ReciprocityTheory.Cheb.ehold_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:15.864682+00:00
-- url     : https://prove2.me/theorems/c16cdf26-a323-4a14-a8ad-64bb5dbc6bac
-- title:
--   Cheb: ehold summable
-- statement:
--   The Cheb construction uses the ehold summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/ChebyshevLambdaSubPsiBounded.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/ChebyshevLambdaSubPsiBounded.lean#L16-L21

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

theorem ReciprocityTheory.Cheb.ehold_summable {E : Type} [Field E] [NumberField E] (f : NZIdeal E → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun a : NZIdeal E => ‖f a * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))‖) := by sorry
