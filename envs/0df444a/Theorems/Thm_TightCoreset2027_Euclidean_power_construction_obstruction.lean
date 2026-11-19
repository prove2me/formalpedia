-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_power_construction_obstruction
-- name    : TightCoreset2027.Euclidean.power_construction_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:42:27.444893+00:00
-- url     : https://prove2.me/theorems/dcb3f61c-2869-4053-8993-ce2bc1e7fd50
-- title:
--   General-power hard instances before parameter selection
-- statement:
--   Fix a real exponent $z\ge1$. There is a constant $A_z>0$ with the following property. For positive integers $n,m,L,q$ and an integer $k$, suppose
--
--   $$q+\binom q3<2^L,\qquad n(\lceil n^{z/2}\rceil-1)+m(L+1)\le k.$$
--
--   There is a finite Euclidean dataset in a positive dimension with
--
--   $$|X|=\lceil n^{z/2}\rceil nmq$$
--
--   such that every strong subset coreset with arbitrary nonnegative weights retains more than half its locations whenever $0<\varepsilon<1$ and
--
--   $$\varepsilon\sqrt{nq}L^2<A_z.$$
--
--   The dataset precedes the accuracy and candidate weights. This is the general-power obstruction in §2.5, before choosing integer parameters. It uses the calibrated level displacements and the full ambient exact-$k$ strong-coreset predicate.
-- source:
--   Hu–Huang–Li–Xu, STOC 2027 submission #879, §2.5 General powers, equations (17)–(19), printed pp.19–20 / PDF pp.21–22; construction §§2.1–2.2 and Lemma2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_generalPowers
open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean
 theorem power_construction_obstruction (z : ℝ) (hz : 1 ≤ z) :
    ∃ A : ℝ, 0 < A ∧ ∀ n m L q k : ℕ,
      1 ≤ n → 1 ≤ m → 1 ≤ L → 1 ≤ q →
      q + Nat.choose q 3 < 2 ^ L →
      n * (copyCountZ z n - 1) + m * (L + 1) ≤ k →
      ∃ d : ℕ, 1 ≤ d ∧ ∃ X : Finset (Point d),
        X.card = copyCountZ z n * n * m * q ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 < A →
          ∀ (S : Finset (Point d)) (w : Point d → NNReal),
            IsStrongCoreset z ε k X S w → (X.card : ℝ) / 2 < (S.card : ℝ) := by sorry
end TightCoreset2027.Euclidean
