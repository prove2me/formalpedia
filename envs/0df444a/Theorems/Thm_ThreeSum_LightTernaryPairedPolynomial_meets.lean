-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
-- name    : ThreeSum.LightTernaryPairedPolynomial.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:32.49102+00:00
-- url     : https://prove2.me/theorems/8a616a73-acab-4787-86cd-68e1b718c419
-- title:
--   Light Ternary Paired Polynomial: meets
-- statement:
--   The Light Ternary Paired Polynomial construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L196-L222
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L196-L222

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.meets (m base Λ colsBase : ℕ) (cols : PairedIndex m → ℕ)
    (μ : ℕ → ℤ) {lim : Limits} {P : Program} {p depth : ℕ}
    (hp : P[p]?=some (body m)) (hΛ : 1≤Λ) (hbound : ∀ r, cols r<Λ)
    (hcols : ∀ r, μ (colsBase+(Fintype.equivFin (PairedIndex m) r).val)=(cols r : ℤ))
    (hTspace : base+Λ^4≤lim.space) (hCspace : colsBase+Fintype.card (PairedIndex m)≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (hTabs : ∀ k<Λ^4, |μ (base+k)|≤U)
    (hWord : (polynomial m).coefficient*(U+1)^(polynomial m).degree≤lim.word) :
    Meets lim P p depth [base,Λ,colsBase] μ (time m)
      (fun r ν => r=value (fun q =>
        μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))) ∧ ν=μ) := by sorry
