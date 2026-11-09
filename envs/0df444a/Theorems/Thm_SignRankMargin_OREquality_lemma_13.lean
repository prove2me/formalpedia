-- Prove2me | Theorems.Thm_SignRankMargin_OREquality_lemma_13
-- name    : SignRankMargin.OREquality.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:42:28.010592+00:00
-- url     : https://prove2.me/theorems/9d72d212-11ac-4e37-9aec-78179202e2aa
-- title:
--   Lemma 13 — one-sided spectral witness
-- statement:
--   Let $X,Y$ be finite nonempty sets of sizes $M,N$. Let $d\ge2$ be an integer and $L\ge1$ a real number. Suppose the Boolean matrix $F:X\times Y\to\{0,1\}$ has at most $(dL)^{-6d}MN$ ones. If there exists a real matrix $A$ of the same size satisfying
--
--   $$
--   A(x,y)\le-1\quad\text{whenever }F(x,y)=0,\qquad
--   \frac1{MN}\sum_{x,y}|A(x,y)|\le L,\qquad
--   \|A\|_{\mathrm{op}}\le\frac{\sqrt{MN}}d,
--   $$
--
--   then
--
--   $$
--   \operatorname{signRank}(F)\ge d.
--   $$
--
--   The operator norm is the Euclidean $\ell_2\to\ell_2$ norm. The witness need not have any specified signs at one-entries of $F$. Rectangular matrices and arbitrary real $L\ge1$ are included. This milestone provides the lower-bound criterion applied in the goal theorem.
--
--   **Formalization Note** The norm is taken on the continuous linear map associated to $A$ between real Euclidean spaces, never on a matrix with an implicit norm instance.
--
--   Differences from the source:
--   - encoding: finite nonempty row and column sets and uniform pair average → Fintype and Nonempty instances; explicit double sum divided by the product of cardinalities; reason: represents exactly the finite uniform average and its positive denominators
--   - encoding: density factor (dL)^(-6d) and Euclidean operator norm of a rectangular real matrix → reciprocal of the real positive power ((d : ℝ)*L)^(6*d), and norm of (Matrix.toEuclideanLin A).toContinuousLinearMap; decidable equality for column indices; reason: dL is at least two, so reciprocal powers equal the negative integer power; the map acts by the same matrix on Euclidean coordinates and finite equality is decidable
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Lemma 13, p. 12; proof pp. 12–13

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_Geometry

namespace SignRankMargin.OREquality

/-- Lemma 13, p.12. The norm is that of the continuous linear map between Euclidean spaces,
not an entrywise matrix norm. The reciprocal positive power is (dL)^(-6d). -/
theorem lemma_13 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Nonempty X] [Nonempty Y] (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (F : Matrix X Y Bool)
    (hsparse : (oneCount F : ℝ) ≤ (((d : ℝ) * L) ^ (6 * d))⁻¹ *
      (Fintype.card X : ℝ) * (Fintype.card Y : ℝ))
    (hwitness : ∃ A : Matrix X Y ℝ,
      (∀ x y, F x y = false → A x y ≤ -1) ∧
      uniformAverage (fun x y => |A x y|) ≤ L ∧
      ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤
        Real.sqrt ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ)) / (d : ℝ)) :
    d ≤ signRank F := by sorry

end SignRankMargin.OREquality
