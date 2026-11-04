-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_body_ends
-- name    : ThreeSum.LightTernaryPairedPolynomial.body_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:30.992205+00:00
-- url     : https://prove2.me/theorems/c3e1a5cc-20fd-45e3-b4c2-6c8e04af2261
-- title:
--   Light Ternary Paired Polynomial: body ends
-- statement:
--   The Light Ternary Paired Polynomial construction uses the body ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L125-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L125-L135

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Theorems.Thm_ThreeSum_LightMomentDeterminant_body_ends

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.body_ends (m : ℕ) (T : Quad m → ℤ) (σ : State) {lim : Limits} {P : Program} {depth : ℕ}
    (U : ℤ) (hU : 0≤U)
    (hSafe : ∀ j, (atoms m j).Safe lim σ)
    (hAbs : ∀ j, |(atoms m j).val σ|≤U)
    (hWord : (polynomial m).coefficient*(U+1)^(polynomial m).degree≤lim.word)
    (hRead : ∀ q, (atomExpr m q).val σ=T q) :
    Ends lim P depth (body m) σ (time m) (fun τ => τ.loc 0=value T ∧ τ.mem=σ.mem) := by sorry
