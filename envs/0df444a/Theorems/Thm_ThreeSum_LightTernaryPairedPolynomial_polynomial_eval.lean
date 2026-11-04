-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_polynomial_eval
-- name    : ThreeSum.LightTernaryPairedPolynomial.polynomial_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:01.490055+00:00
-- url     : https://prove2.me/theorems/74107264-39d6-40b5-97b2-9a359ef20b95
-- title:
--   Light Ternary Paired Polynomial: polynomial eval
-- statement:
--   The Light Ternary Paired Polynomial construction uses the polynomial eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L28-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean#L28-L42

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPolynomial.polynomial_eval (m : ℕ) (x : ℕ → ℤ) :
    (polynomial m).eval x =
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        ((Equiv.Perm.sign σ : ℤ)*(Equiv.Perm.sign τ : ℤ)) *
          ∏ i : Fin m, x (encode (channel σ τ i)) := by sorry
