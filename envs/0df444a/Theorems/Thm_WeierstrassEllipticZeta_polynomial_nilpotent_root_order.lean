-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_polynomial_nilpotent_root_order
-- name    : WeierstrassEllipticZeta.polynomial_nilpotent_root_order
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-11T00:21:55.7705+00:00
-- url     : https://prove2.me/theorems/35842a99-e337-40f6-94fb-0afee3b6109d
-- title:
--   Exact root-order calculus at a nilpotent scalar perturbation
-- statement:
--   Let $K$ be a field, $A$ a commutative ring, and $\phi:K\to A$ a unital ring homomorphism. Suppose $x\in A$, $z\in K$ and $d\in\mathbb N$ satisfy $(x-\phi(z))^d=0$. Let $q\in K[T]$ be nonzero, and let $r$ be its root multiplicity at $z$. Write $q_\phi(x)$ for evaluation with coefficients mapped through $\phi$.
--
--   There is a unit $u\in A^\times$ such that
--   $$
--   q_\phi(x)=(x-\phi(z))^r u.
--   $$
--   For every natural number $k$,
--   $$
--   q_\phi(x)^k=0\quad\Longleftrightarrow\quad (x-\phi(z))^{rk}=0.
--   $$
--   Consequently $q_\phi(x)^k=0$ whenever $d\le rk$.
--
--   The polynomial must be nonzero because its finite root multiplicity is used. The ring $A$ need not be nonzero or finite dimensional. The statement includes $r=0$ and $k=0$. If $r>0$, the displayed bound yields vanishing at the ceiling of $d/r$; the exact equivalence also records information when the supplied exponent $d$ is not minimal.
-- source:
--   Derived algebra lemma, proved here using polynomial root factorization and nonvanishing of the residual factor: Mathlib, Algebra/Polynomial/Div.lean, lines 552-556 and 641-653, at revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L552-L556 and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L641-L653. In a commutative ring, a nonzero polynomial evaluated at a nilpotent scalar perturbation equals the scalar shift to its root multiplicity times a unit. Consequently its kth power vanishes exactly when the shift to multiplicity times k vanishes. This is a supporting calculation derived for the Senthil Kumar mission, not quoted from the article. The nonzero polynomial hypothesis is essential; no nontriviality or finite-dimensionality of the target ring is required. No new definitions or platform theorem dependencies.

import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Nilpotent.Basic

theorem WeierstrassEllipticZeta.polynomial_nilpotent_root_order
    (K A : Type*) [Field K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (d : ℕ) (hx : (x - φ z) ^ d = 0)
    (q : Polynomial K) (hq : q ≠ 0) :
    ∃ u : Aˣ,
      q.eval₂ φ x = (x - φ z) ^ q.rootMultiplicity z * (u : A) ∧
      (∀ k : ℕ, (q.eval₂ φ x) ^ k = 0 ↔
        (x - φ z) ^ (q.rootMultiplicity z * k) = 0) ∧
      ∀ k : ℕ, d ≤ q.rootMultiplicity z * k → (q.eval₂ φ x) ^ k = 0 := by sorry
