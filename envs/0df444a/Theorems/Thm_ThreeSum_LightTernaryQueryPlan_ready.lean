-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryQueryPlan_ready
-- name    : ThreeSum.LightTernaryQueryPlan.ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:26:52.495259+00:00
-- url     : https://prove2.me/theorems/350128f4-5ea4-460f-8888-7ea6552de479
-- title:
--   Light Ternary Query Plan: ready
-- statement:
--   The Light Ternary Query Plan construction uses the ready property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryQueryPlan.lean#L38-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryQueryPlan.lean#L38-L62

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSetup
import Definitions.Def_Submission_ThreeSum_LightTernaryQueryPlan
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightTernaryNearPair

theorem ThreeSum.LightTernaryQueryPlan.ready {lim : Limits} {N rows : ℕ} {c : Config} {μ : ℕ→ℤ}
    {Q : TritWord N} {bankWords nearWords : ℕ→TritWord N} {source : TritWord N→ℤ}
    (R : Resources lim rows c source)
    (hread : ∀ j<rows, μ (c.a+j)=(address (nearWords j) : ℤ))
    (hbankRead : ∀ j<c.nb, μ (c.bank+j)=(address (bankWords j) : ℤ))
    (hactiveRead : ∀ i<N, μ (c.activeBase+i)=1)
    (hpowers : Powers μ c.powers (2*N))
    (hbankValues : ∀ j<c.nb, μ (c.bv+j)=binomialZeta source (bankWords j))
    (hbankSorted : ∀ j k, j<k → k<c.nb → address (bankWords j)<address (bankWords k))
    (hnearSorted : ∀ j k, j<k → k<rows → address (nearWords j)<address (nearWords k))
    (hbankPresent : ∀ W, rank W≤c.T → ∃ j<c.nb, bankWords j=W)
    (hnearPresent : ∀ W, Below W Q → c.T<rank W → ∃ j<rows, nearWords j=W)
    (hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ c.T<rank (nearWords j)) :
    Ready lim rows c μ Q bankWords nearWords source := by sorry
