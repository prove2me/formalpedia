-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_et_normal_form
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.et_normal_form
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:31:41.3466+00:00
-- url     : https://prove2.me/theorems/2b600790-0cca-4337-b897-0cc8b0755134
-- title:
--   Proposition 8.1: E–T normal form
-- statement:
--   Let $E=HS^3\omega^3$ with its exact phase and let $\mathcal C=\langle H,S,\omega I\rangle$. Every exact single-qubit Clifford+$T$ operator has a unique expression
--
--   $$
--   (T\mid\varepsilon)(ET\mid E^2T)^*C,\qquad C\in\mathcal C.
--   $$
--   The terminal is an operator, and the actual number of displayed $T$ letters is minimal among all exact Clifford+$T$ decompositions. One fixed finite suffix-table algorithm converts every symbolic input of length $n$ to this syntax in at most $B(n+1)$ primitive operations for an input-independent $B>0$.
--
--   This preserves all existence, uniqueness, optimality and symbolic algorithm clauses of the alternative normal form.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 11, Proposition 8.1: E–T normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Proposition 8.1, PDF p.11: all four clauses of the E-T normal-form result,
including the actual finite symbolic algorithm with input-uniform linear cost. -/
theorem et_normal_form :
    (∀ U : Mat, CliffordT U → ∃! M : NormalForm, normalValue cliffordE cliffordE2 M = U) ∧
    (∀ (M : NormalForm) (w : List Input),
      inputWordMatrix w = normalValue cliffordE cliffordE2 M → normalTCount M ≤ inputTCount w) ∧
    LinearNormalizer (normalTokens cliffordE cliffordE2) (normalValue cliffordE cliffordE2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
