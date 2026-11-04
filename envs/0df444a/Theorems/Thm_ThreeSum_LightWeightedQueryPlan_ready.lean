-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedQueryPlan_ready
-- name    : ThreeSum.LightWeightedQueryPlan.ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:27:09.236086+00:00
-- url     : https://prove2.me/theorems/066ec7f4-621b-4b3d-ac32-0780aafad9e0
-- title:
--   Light Weighted Query Plan: ready
-- statement:
--   The Light Weighted Query Plan construction uses the ready property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryPlan.lean#L44-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryPlan.lean#L44-L68

import Definitions.Def_Submission_Weighted_WantedQuery
import Definitions.Def_Submission_Weighted_NearSetup
import Definitions.Def_Submission_Weighted_QueryPlan
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedQueryPlan
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.LightWeightedNearPair

theorem ThreeSum.LightWeightedQueryPlan.ready {lim : Limits} {N rows : ℕ} {c : Config} {μ : ℕ→ℤ}
    {Q : TritWord N} {bankWords nearWords : ℕ→TritWord N} {source : TritWord N→ℤ}
    (R : Resources lim rows c source)
    (hread : ∀ j<rows, μ (c.a+j)=(address (nearWords j) : ℤ))
    (hbankRead : ∀ j<c.nb, μ (c.bank+j)=(address (bankWords j) : ℤ))
    (hactiveRead : ∀ i<N, μ (c.activeBase+i)=1)
    (hpowers : Powers μ c.powers (2*N))
    (hbankValues : ∀ j<c.nb, μ (c.bv+j)=binomialZeta source (bankWords j))
    (hbankSorted : ∀ j k, j<k → k<c.nb → address (bankWords j)<address (bankWords k))
    (hnearSorted : ∀ j k, j<k → k<rows → address (nearWords j)<address (nearWords k))
    (hbankPresent : ∀ W, cacheCost W≤c.T → ∃ j<c.nb, bankWords j=W)
    (hnearPresent : ∀ W, Below W Q → c.T<cacheCost W → ∃ j<rows, nearWords j=W)
    (hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ c.T<cacheCost (nearWords j)) :
    Ready lim rows c μ Q bankWords nearWords source := by sorry
