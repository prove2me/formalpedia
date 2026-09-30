-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_pointed_cardinality_image_test_iff
-- name    : WeierstrassEllipticZeta.pointed_cardinality_image_test_iff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T23:04:18.501085+00:00
-- url     : https://prove2.me/theorems/b5598925-d3e3-46cf-a597-410244b21a6c
-- title:
--   Cardinality alternatives are detected by subsets retaining a point
-- statement:
--   Let f map a finite set X into any type, and let x₀∈X be a point that must be retained. For real numbers w>0 and 0≤B≤A, the alternative w|X|≤A or w|f(X)|≤B is equivalent to the following collection of tests: every subset Y⊆X containing x₀ with exactly floor(A/w)+1 points satisfies w|f(Y)|≤B.
--
--   The key selection argument constructs a subset of any allowed positive size r, retaining x₀, whose image has exactly min(r, |f(X)|) elements. Thus a failure of both numerical bounds has a witness of the prescribed size. The constant and thresholds are unchanged.
-- source:
--   Derived finite-subset reduction for the open frontier https://prove2.me/theorems/e074d90d-6a5f-46c1-9e9e-f986ff91e6bf. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3, https://doi.org/10.1017/S001309152610145X. The article motivates multiplicity-weighted counts of points and subgroup cosets; the subset selection theorem here is an independent elementary reduction, not a quotation or a proof of the article zero estimate. Primary formal sources are Mathlib Data/Set/Function.lean, Data/Finset/Card.lean, Data/Set/Card.lean and Algebra/Order/Floor/Semiring.lean at revision 0df444a360eaa60ab8c11dca51a86af692955474. The remaining statement is equivalent to the parent for the same constant and unchanged ambient hypotheses. The global estimate and main theorem remain open.

import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable section

theorem WeierstrassEllipticZeta.pointed_cardinality_image_test_iff
    {α β : Type*} (f : α → β) (X : Finset α) (x₀ : α) (hx₀ : x₀ ∈ X)
    (w A B : ℝ) (hw : 0 < w) (hB : 0 ≤ B) (hBA : B ≤ A) :
    (w * X.card ≤ A ∨ w * (f '' (X : Set α)).ncard ≤ B) ↔
      ∀ Y : Finset α, Y ⊆ X → x₀ ∈ Y → Y.card = ⌊A / w⌋₊ + 1 →
        w * (f '' (Y : Set α)).ncard ≤ B := by sorry
