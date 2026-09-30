-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_polynomial_nilpotency_index
-- name    : WeierstrassEllipticZeta.polynomial_nilpotency_index
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-11T04:42:02.478012+00:00
-- url     : https://prove2.me/theorems/5db72280-41df-42e6-abe8-215fc10d0d8a
-- title:
--   Exact nilpotency index of polynomial evaluation from root multiplicity
-- statement:
--   Let $K$ be a field, let $A$ be a commutative ring, and let $\phi:K\to A$ be a unital ring homomorphism. Let $x\in A$, $z\in K$ and $d\ge0$ satisfy $(x-\phi(z))^d=0$. Fix a nonzero polynomial $q\in K[T]$, and write
--   $$
--   y=x-\phi(z),\qquad n=\operatorname{nilpotencyClass}(y),\qquad
--   r=\operatorname{ord}_z(q).
--   $$
--   Here $n$ is the least nonnegative exponent with $y^n=0$, and $r$ is the multiplicity of the root $z$ in $q$. Write $E(q)=q_\phi(x)$ for evaluation through $\phi$.
--
--   For every nonnegative integer $k$,
--   $$
--   E(q)^k=0\quad\Longleftrightarrow\quad n\le rk.
--   $$
--   If $r>0$, then $E(q)$ is nilpotent and its exact nilpotency class is
--   $$
--   \operatorname{nilpotencyClass}(E(q))
--   =\left\lceil\frac nr\right\rceil
--   =\left\lfloor\frac{n+r-1}{r}\right\rfloor.
--   $$
--   The formal formula uses natural-number division. The first equivalence also covers $r=0$ and $k=0$; the index formula assumes $r>0$. No characteristic, finite-dimensionality or nontriviality assumption is imposed on the target. In a trivial target ring, both nilpotency classes are zero. The hypothesis $q\ne0$ is required to use its finite root multiplicity.
-- source:
--   Derived supporting algebra lemma for the Senthil Kumar mission, using Proved theorem WeierstrassEllipticZeta.polynomial_nilpotent_root_order (35842a99-e337-40f6-94fb-0afee3b6109d). At Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, nilpotencyClass and pow_nilpotencyClass are in RingTheory/Nilpotent/Defs.lean lines 61-81; ceilDiv_le_iff_le_mul and Nat.ceilDiv_eq_add_pred_div are in Algebra/Order/Floor/Div.lean lines 176 and 190-197. Official references: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nilpotent/Defs.html#nilpotencyClass and https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Floor/Div.html#ceilDiv_le_iff_le_mul . For a nonzero polynomial with root multiplicity r at z and a nilpotent shift x-phi(z) of class n, its evaluated kth power vanishes exactly when n <= r*k. If r>0, its exact nilpotency class is ceil(n/r), expressed as (n+r-1)/r in natural-number division. Works over an arbitrary field and any commutative target ring, including trivial rings. No characteristic or finite-dimensionality assumption, and no new definitions.

import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Nilpotent.Basic

theorem WeierstrassEllipticZeta.polynomial_nilpotency_index
    (K A : Type*) [Field K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (d : ℕ) (hx : (x - φ z) ^ d = 0)
    (q : Polynomial K) (hq : q ≠ 0) :
    let n := nilpotencyClass (x - φ z)
    let r := q.rootMultiplicity z
    (∀ k : ℕ, (q.eval₂ φ x) ^ k = 0 ↔ n ≤ r * k) ∧
      (0 < r → IsNilpotent (q.eval₂ φ x) ∧
        nilpotencyClass (q.eval₂ φ x) = (n + r - 1) / r) := by sorry
