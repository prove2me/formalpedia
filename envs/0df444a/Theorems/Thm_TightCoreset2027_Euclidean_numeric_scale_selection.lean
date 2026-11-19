-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_numeric_scale_selection
-- name    : TightCoreset2027.Euclidean.numeric_scale_selection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:42:17.563118+00:00
-- url     : https://prove2.me/theorems/190b0cb7-d4b4-46d4-b6fa-ee630e5f8a50
-- title:
--   Selecting feasible integer parameters or the boundary regime
-- statement:
--   Fix $z\ge1$ and a positive error-scale constant $A$. There are a constant $c>0$ and a nonnegative integer $b$, independent of $k$ and $\varepsilon$, such that the following alternative holds for every $k\ge1$ and $0<\varepsilon<1$. Put
--
--   $$F=\frac{c\min\{k^{(2z+2)/(z+2)}\varepsilon^{-2},\;k\varepsilon^{-z-2}\}}{[\log(2+1/\varepsilon)]^b}.$$
--
--   Either $F\le k\varepsilon^{-2}$, or positive integers $n,m,L,q$ satisfy the coding condition, the exact center budget and the error constraint, with
--
--   $$q+\binom q3<2^L,\quad n(\lceil n^{z/2}\rceil-1)+m(L+1)\le k,\quad\varepsilon\sqrt{nq}L^2<A,\quad F\le\tfrac12\lceil n^{z/2}\rceil nmq.$$
--
--   This isolates the arithmetic and rounding component of the source parameter choice. A larger logarithmic loss is permitted here; using a power of $\log(2+1/\varepsilon)$ alone fits the goal with zero degree on the $k$ logarithm. The alternative states exactly when the boundary lower bound suffices and when feasible construction parameters supply the desired cardinality.
-- source:
--   Hu–Huang–Li–Xu, STOC2027 submission879, §2.3 parameter choice and rounding, printed pp.15–16 / PDF pp.17–18, and §2.5 small/larger-error parameter choices and boundary cases, printed pp.20–21 / PDF pp.22–23; Theorem1.2 and footnote1 logarithmic convention; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_generalPowers
open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean
 theorem numeric_scale_selection (z : ℝ) (hz : 1 ≤ z) (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℕ,
      ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
        c * lowerBoundScale z k ε / (Real.log (2 + 1 / ε)) ^ b ≤
          (k : ℝ) * Real.rpow ε (-2) ∨
        ∃ n m L q : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ 1 ≤ L ∧ 1 ≤ q ∧
          q + Nat.choose q 3 < 2 ^ L ∧
          n * (copyCountZ z n - 1) + m * (L + 1) ≤ k ∧
          ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 < A ∧
          c * lowerBoundScale z k ε / (Real.log (2 + 1 / ε)) ^ b ≤
            ((copyCountZ z n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) / 2 := by sorry
end TightCoreset2027.Euclidean
