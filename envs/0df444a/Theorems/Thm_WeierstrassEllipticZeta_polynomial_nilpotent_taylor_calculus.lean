-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_polynomial_nilpotent_taylor_calculus
-- name    : WeierstrassEllipticZeta.polynomial_nilpotent_taylor_calculus
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-11T02:55:28.195483+00:00
-- url     : https://prove2.me/theorems/978e04a7-bb71-4b68-b1d0-3a57aacf0696
-- title:
--   Finite Taylor expansion and exact Hasse-jet criteria for polynomial evaluation
-- statement:
--   Let $K$ and $A$ be commutative rings, let $\phi:K\to A$ be a unital ring homomorphism, and fix $x\in A$, $z\in K$ and a nonnegative integer $n$. Write $E(q)=q_\phi(x)$ for polynomial evaluation. Assume the exact kernel criterion
--   $$
--   E(q)=0\quad\Longleftrightarrow\quad (T-z)^n\mid q
--   $$
--   for every $q\in K[T]$.
--
--   Let $D^{[i]}q$ be the $i$th Hasse derivative: $(D^{[i]}q)(z)$ is the coefficient of $T^i$ in $q(z+T)$. Then every polynomial satisfies the finite Taylor formula
--   $$
--   E(q)=\sum_{i=0}^{n-1}\phi\big((D^{[i]}q)(z)\big)\,(x-\phi(z))^i.
--   $$
--   Moreover,
--   $$
--   E(q)=0\quad\Longleftrightarrow\quad
--   (D^{[i]}q)(z)=0\ \text{for every }0\le i<n,
--   $$
--   and, for every pair $q,r\in K[T]$,
--   $$
--   E(q)=E(r)\quad\Longleftrightarrow\quad
--   (D^{[i]}q)(z)=(D^{[i]}r)(z)\ \text{for every }0\le i<n.
--   $$
--   Thus the first $n$ Taylor coefficients exactly determine polynomial evaluation at $x$. No characteristic, integrality or finite-dimensionality assumption is needed. Trivial rings and $n=0$ are allowed; for $n=0$ the sum and jet conditions are empty, and the kernel hypothesis forces every evaluation to be zero.
-- source:
--   Derived supporting algebra lemma for the Senthil Kumar mission, not quoted from the article. Exact sources in Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: Polynomial.taylor_coeff, taylorEquiv and taylor_apply in Algebra/Polynomial/Taylor.lean (lines 46, 68-76 and 192-202); Polynomial.X_pow_dvd_iff in Algebra/Polynomial/Div.lean (44-55); Polynomial.eval₂_eq_sum_range' and eval₂_comp in Algebra/Polynomial/Eval/Degree.lean (49-54 and 205-206); map_dvd_iff in Algebra/Ring/Divisibility/Basic.lean (29-31). Links: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Taylor.lean#L68-L76 and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L44-L55. Under an exact evaluation-kernel hypothesis ((T-z)^n), evaluation is a finite Taylor sum; zero and equality are characterized by the first n Hasse derivatives at z. Both coefficient and target rings may be arbitrary commutative rings, including trivial rings; n=0 is allowed. No new definitions or platform theorem dependencies.

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div

theorem WeierstrassEllipticZeta.polynomial_nilpotent_taylor_calculus
    (K A : Type*) [CommRing K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (n : ℕ)
    (hker : ∀ q : Polynomial K,
      q.eval₂ φ x = 0 ↔ (Polynomial.X - Polynomial.C z) ^ n ∣ q) :
    (∀ q : Polynomial K, q.eval₂ φ x =
      ∑ i ∈ Finset.range n, φ ((Polynomial.hasseDeriv i q).eval z) * (x - φ z) ^ i) ∧
    (∀ q : Polynomial K,
      q.eval₂ φ x = 0 ↔ ∀ i < n, (Polynomial.hasseDeriv i q).eval z = 0) ∧
    ∀ q r : Polynomial K, q.eval₂ φ x = r.eval₂ φ x ↔
      ∀ i < n, (Polynomial.hasseDeriv i q).eval z = (Polynomial.hasseDeriv i r).eval z := by sorry
