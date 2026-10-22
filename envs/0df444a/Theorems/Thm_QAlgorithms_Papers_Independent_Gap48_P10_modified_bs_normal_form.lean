-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_modified_bs_normal_form
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.modified_bs_normal_form
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:34:02.716048+00:00
-- url     : https://prove2.me/theorems/d97d5f73-c04f-4556-a109-c19f32d8c3cd
-- title:
--   §8.3 unnumbered: corrected unique BS form
-- statement:
--   Every exact single-qubit Clifford+$T$ operator has a unique expression of the corrected Bocharov–Svore syntax
--
--   $$
--   (\varepsilon\mid T)(HT\mid HSHT)^*C,\qquad C\in\mathcal C.
--   $$
--   The actual displayed $T$-count is minimal among all exact Clifford+$T$ decompositions. One fixed finite suffix-table machine symbolically converts every input of length $n$ to this syntax in at most $B(n+1)$ primitive operations for one input-independent $B>0$.
--
--   This states the result for equation (24), preserving existence, uniqueness, optimality and linear symbolic normalization.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 12, §8.3 unnumbered: corrected unique BS form

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Section 8.3, equation (24), PDF p.12: corrected BS syntax uses HT or HSHT.
All existence, uniqueness, T-optimality and efficiency clauses are retained.
The false printed E-coordinate range on p.11 is not an assumption. -/
theorem modified_bs_normal_form :
    (∀ U : Mat, CliffordT U → ∃! M : NormalForm, normalValue cliffordH cliffordHSH M = U) ∧
    (∀ (M : NormalForm) (w : List Input),
      inputWordMatrix w = normalValue cliffordH cliffordHSH M → normalTCount M ≤ inputTCount w) ∧
    LinearNormalizer (normalTokens cliffordH cliffordHSH) (normalValue cliffordH cliffordHSH) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
