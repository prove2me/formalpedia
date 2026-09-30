-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_nilpotent_shift_geometric_inverse
-- name    : WeierstrassEllipticZeta.nilpotent_shift_geometric_inverse
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T22:06:44.792355+00:00
-- url     : https://prove2.me/theorems/132b4cca-52bf-4c01-bba2-bbde0773c39f
-- title:
--   Finite geometric inverse of a nonzero scalar plus a nilpotent
-- statement:
--   Let $K$ be a field, $A$ a commutative ring, and $\phi:K\to A$ a unital ring homomorphism giving its scalar structure. Suppose $x\in A$ satisfies $x^N=0$ for some integer $N\ge0$, and let $c\in K$ be nonzero. Define
--   $$
--   b=\phi(c^{-1})\sum_{j=0}^{N-1}(-\phi(c^{-1})x)^j,
--   $$
--   where scalars act through the algebra structure and the sum is empty when $N=0$.
--   Then
--   $$
--   (x+\phi(c))b=b(x+\phi(c))=1.
--   $$
--   In particular, $x+\phi(c)$ is a unit of $A$, with the displayed explicit inverse. The statement allows the zero algebra; the hypothesis $x^0=0$ forces precisely this case when $N=0$.
-- source:
--   Derived algebra lemma, proved here from the finite geometric sum identity mul_neg_geom_sum in Mathlib, Algebra/Ring/GeomSum.lean, lines 240-246 at revision 0df444a360eaa60ab8c11dca51a86af692955474: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Ring/GeomSum.lean#L240-L246. It supplies an explicit finite inverse of a nonzero scalar plus a nilpotent element in a commutative algebra over a field. This supporting lemma for the Senthil Kumar mission is not quoted from the article. No new definitions or platform theorem dependencies.

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring

theorem WeierstrassEllipticZeta.nilpotent_shift_geometric_inverse
    (K A : Type*) [Field K] [CommRing A] (φ : K →+* A)
    (x : A) (N : ℕ) (hx : x ^ N = 0) (c : K) (hc : c ≠ 0) :
    let b := φ c⁻¹ * ∑ i ∈ Finset.range N, (-(φ c⁻¹ * x)) ^ i
    (x + φ c) * b = 1 ∧ b * (x + φ c) = 1 ∧ IsUnit (x + φ c) := by sorry
