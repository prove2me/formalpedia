-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_atomExpr_memory
-- name    : ThreeSum.LightTernaryPairedPolynomial.atomExpr_memory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:34.00577+00:00
-- url     : https://prove2.me/theorems/142db3b2-1794-4921-b990-01209026c96f
-- title:
--   Light Ternary Paired Polynomial: atom Expr memory
-- statement:
--   The Light Ternary Paired Polynomial construction uses the atom Expr memory property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L137-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L137-L144

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.atomExpr_memory (m base Λ colsBase : ℕ) (cols : PairedIndex m → ℕ)
    (μ : ℕ → ℤ)
    (hcols : ∀ r, μ (colsBase+(Fintype.equivFin (PairedIndex m) r).val)=(cols r : ℤ))
    (q : Quad m) :
    (atomExpr m q).val ⟨frame [base,Λ,colsBase],μ⟩ =
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)) := by sorry
