-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_polynomial_nilpotent_derivative_calculus
-- name    : WeierstrassEllipticZeta.polynomial_nilpotent_derivative_calculus
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-11T03:40:07.882868+00:00
-- url     : https://prove2.me/theorems/a7ce1a01-10f2-40a7-b4dc-06eeffb36a9d
-- title:
--   Ordinary Taylor expansion and exact derivative criteria for polynomial evaluation
-- statement:
--   Let $K$ be a field of characteristic zero, let $A$ be a commutative ring, and let $\phi:K\to A$ be a unital ring homomorphism. Fix $x\in A$, $z\in K$ and a nonnegative integer $n$. Write $E(q)=q_\phi(x)$ for polynomial evaluation, and assume the exact kernel criterion
--   $$
--   E(q)=0\quad\Longleftrightarrow\quad (T-z)^n\mid q
--   $$
--   for every $q\in K[T]$.
--
--   Write $q^{(i)}$ for the $i$th ordinary polynomial derivative, with $q^{(0)}=q$. Then
--   $$
--   E(q)=\sum_{i=0}^{n-1}\phi\!\left(\frac{q^{(i)}(z)}{i!}\right)(x-\phi(z))^i.
--   $$
--   Moreover,
--   $$
--   E(q)=0\quad\Longleftrightarrow\quad q^{(i)}(z)=0\text{ for every }0\le i<n,
--   $$
--   and, for all $q,r\in K[T]$,
--   $$
--   E(q)=E(r)\quad\Longleftrightarrow\quad
--   q^{(i)}(z)=r^{(i)}(z)\text{ for every }0\le i<n.
--   $$
--   The factorial divisions take place in $K$ before applying $\phi$. No finite-dimensionality or nontriviality assumption is imposed on $A$. The case $n=0$ is included: the sum and derivative conditions are empty, and the kernel hypothesis forces all evaluations to be zero.
-- source:
--   Derived supporting algebra lemma for the Senthil Kumar mission. Uses the Proved platform theorem WeierstrassEllipticZeta.polynomial_nilpotent_taylor_calculus (978e04a7-bb71-4b68-b1d0-3a57aacf0696) and Polynomial.factorial_smul_hasseDeriv in pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, Algebra/Polynomial/HasseDeriv.lean lines 128-146: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/HasseDeriv.lean#L128-L146. Over a characteristic-zero field K, ordinary derivatives divided by factorials give the finite Taylor evaluation formula under exact kernel ((T-z)^n), and ordinary derivatives of orders below n exactly detect zero and equality. The target is any commutative ring, including a trivial ring, with explicit coefficient homomorphism. The case n=0 is included. No new definitions.

import Mathlib.Algebra.Polynomial.HasseDeriv

theorem WeierstrassEllipticZeta.polynomial_nilpotent_derivative_calculus
    (K A : Type*) [Field K] [CharZero K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (n : ℕ)
    (hker : ∀ q : Polynomial K,
      q.eval₂ φ x = 0 ↔ (Polynomial.X - Polynomial.C z) ^ n ∣ q) :
    (∀ q : Polynomial K, q.eval₂ φ x =
      ∑ i ∈ Finset.range n,
        φ (((Polynomial.derivative^[i]) q).eval z / (i.factorial : K)) * (x - φ z) ^ i) ∧
    (∀ q : Polynomial K,
      q.eval₂ φ x = 0 ↔ ∀ i < n, ((Polynomial.derivative^[i]) q).eval z = 0) ∧
    ∀ q r : Polynomial K, q.eval₂ φ x = r.eval₂ φ x ↔
      ∀ i < n, ((Polynomial.derivative^[i]) q).eval z =
        ((Polynomial.derivative^[i]) r).eval z := by sorry
