-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_atomExpr_safe
-- name    : ThreeSum.LightTernaryPairedPolynomial.atomExpr_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:46.91489+00:00
-- url     : https://prove2.me/theorems/4178331c-cd23-4f19-8144-c398982a0e44
-- title:
--   Light Ternary Paired Polynomial: atom Expr safe
-- statement:
--   The Light Ternary Paired Polynomial construction uses the atom Expr safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L146-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L146-L194

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.atomExpr_safe (m base Λ colsBase : ℕ) (cols : PairedIndex m → ℕ)
    (μ : ℕ → ℤ) {lim : Limits}
    (hΛ : 1≤Λ) (hbound : ∀ r, cols r<Λ)
    (hcols : ∀ r, μ (colsBase+(Fintype.equivFin (PairedIndex m) r).val)=(cols r : ℤ))
    (hTspace : base+Λ^4≤lim.space) (hCspace : colsBase+Fintype.card (PairedIndex m)≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word) (q : Quad m) :
    (atomExpr m q).Safe lim ⟨frame [base,Λ,colsBase],μ⟩ := by sorry
