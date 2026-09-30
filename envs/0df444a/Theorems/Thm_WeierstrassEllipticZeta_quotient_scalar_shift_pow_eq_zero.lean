-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_quotient_scalar_shift_pow_eq_zero
-- name    : WeierstrassEllipticZeta.quotient_scalar_shift_pow_eq_zero
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T20:41:30.738826+00:00
-- url     : https://prove2.me/theorems/09023e0b-4368-40fc-8be6-9cdec615e7ef
-- title:
--   Scalar-shift nilpotence in a quotient from a generalized eigenvector
-- statement:
--   Let $K$ and $B$ be commutative rings, with $B$ a $K$-algebra. Let $V$ be a $K$-module, let $e:B\to V$ be an injective $K$-linear map, and let $P:V\to V$ be $K$-linear. Fix $\alpha,\varepsilon\in B$, an ideal $J\subset B$, a scalar $z\in K$, and an integer $n\ge0$.
--
--   Assume that
--   $$
--   a\in J\quad\Longleftrightarrow\quad\varepsilon a=0,
--   \qquad P(e(a))=e(\alpha a)
--   \quad(a\in B),
--   $$
--   and that $e(\varepsilon)$ lies in the generalized $z$-eigenspace of order $n$, meaning
--   $$
--   (P-z\operatorname{id})^n e(\varepsilon)=0.
--   $$
--   Then in the quotient $K$-algebra $B/J$,
--   $$
--   \bigl([\alpha]-z\cdot1_{B/J}\bigr)^n=0.
--   $$
--   Neither finite-dimensionality nor surjectivity of $e$ is required. The assertion includes $n=0$, in which case the hypotheses force the quotient to be the zero ring.
-- source:
--   Derived algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. An injective linear coordinate map intertwining multiplication by alpha with an operator P transfers a generalized eigenvector relation for epsilon into vanishing of the corresponding scalar shift to the same power in the quotient by the multiplication annihilator of epsilon. Works over arbitrary commutative base rings with no finite-dimensionality assumption. No new definitions or platform theorem dependencies.

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

theorem WeierstrassEllipticZeta.quotient_scalar_shift_pow_eq_zero
    (K B V : Type*) [CommRing K] [CommRing B] [Algebra K B]
    [AddCommGroup V] [Module K V] (e : B →ₗ[K] V)
    (he : Function.Injective e) (P : Module.End K V)
    (α ε : B) (J : Ideal B) (z : K) (n : ℕ)
    (hJ : ∀ a, a ∈ J ↔ ε * a = 0)
    (hP : ∀ a, P (e a) = e (α * a))
    (hε : e ε ∈ Module.End.genEigenspace P z n) :
    (Ideal.Quotient.mk J α - algebraMap K (B ⧸ J) z) ^ n = 0 := by sorry
