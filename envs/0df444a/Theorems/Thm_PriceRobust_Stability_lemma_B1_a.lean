-- Prove2me | Theorems.Thm_PriceRobust_Stability_lemma_B1_a
-- name    : PriceRobust.Stability.lemma_B1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:12.547516+00:00
-- url     : https://prove2.me/theorems/a8526e2c-d6fa-4e76-a669-f31a81be629e
-- title:
--   Lemma B.1(a), Appendix p. 6 — a ZP-matrix below a Z-matrix has a nonnegative inverse
-- statement:
--   Let $A$ be a ZP-matrix and $B$ a Z-matrix with $A\le B$ entrywise. Then $A$ is invertible and its inverse is entrywise nonnegative:
--   $$A^{-1}\ \text{exists and}\ A^{-1}\ge 0.$$
--
--   This is the inverse-positivity of nonsingular M-matrices; in the proof of Theorem 3 it gives $R^{-1}_{\mathcal N(i),\mathcal N(i)}\ge 0$.
--
--   **Formalization Note** The matrix $B$ belongs to the shared preamble of Lemma B.1 and is kept as printed, although part (a) does not use it. Invertibility is stated as $\det A$ being a unit; nonnegativity is entrywise.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), Online Appendix p. 6 (PDF 26), Lemma B.1(a)

import Mathlib
import Definitions.Def_PriceRobust_Stability_ZPMatrix

open Matrix

namespace PriceRobust.Stability

theorem lemma_B1_a {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : IsZPMatrix A) (hB : IsZMatrix B) (hAB : ∀ l m, A l m ≤ B l m) :
    IsUnit A.det ∧ ∀ l m, 0 ≤ A⁻¹ l m := by sorry

end PriceRobust.Stability
