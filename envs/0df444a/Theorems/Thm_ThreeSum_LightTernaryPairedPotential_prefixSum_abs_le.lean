-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_prefixSum_abs_le
-- name    : ThreeSum.LightTernaryPairedPotential.prefixSum_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:58.958325+00:00
-- url     : https://prove2.me/theorems/ba4b0d48-2ce5-4327-9769-be33a690924e
-- title:
--   Light Ternary Paired Potential: prefix Sum abs le
-- statement:
--   The Light Ternary Paired Potential construction uses the prefix Sum abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L51-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L51-L59

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.prefixSum_abs_le (m base Λ : ℕ) (μ : ℕ → ℤ) (U : ℤ) (hU : 0≤U) (hΛ : 1≤Λ)
    (hT : ∀ k<Λ^4, |μ (base+k)|≤U) (i : ℕ) :
    |prefixSum m base Λ μ i| ≤ (i : ℤ)*(polynomial m).bound U := by sorry
