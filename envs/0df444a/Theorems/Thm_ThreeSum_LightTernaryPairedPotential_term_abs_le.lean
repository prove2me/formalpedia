-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_term_abs_le
-- name    : ThreeSum.LightTernaryPairedPotential.term_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:31.393024+00:00
-- url     : https://prove2.me/theorems/29df541a-e137-4cf1-bdd4-b05890655b4c
-- title:
--   Light Ternary Paired Potential: term abs le
-- statement:
--   The Light Ternary Paired Potential construction uses the term abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L42-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L42-L49

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.term_abs_le (m base Λ : ℕ) (μ : ℕ → ℤ) (U : ℤ) (hU : 0≤U) (hΛ : 1≤Λ)
    (hT : ∀ k<Λ^4, |μ (base+k)|≤U) (i : ℕ) :
    |term m base Λ μ i|≤(polynomial m).bound U := by sorry
