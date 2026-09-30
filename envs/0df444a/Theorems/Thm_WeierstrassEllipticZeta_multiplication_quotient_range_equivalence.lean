-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_multiplication_quotient_range_equivalence
-- name    : WeierstrassEllipticZeta.multiplication_quotient_range_equivalence
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T20:02:57.266049+00:00
-- url     : https://prove2.me/theorems/f87004df-9697-47b9-aa80-47d4ca4d4d51
-- title:
--   Multiplication-kernel quotient as the operator range in linear coordinates
-- statement:
--   Let $K$ be a field, let $B$ be a commutative $K$-algebra, and let $V$ be a $K$-vector space. Suppose $e:B\to V$ is a linear isomorphism, $P:V\to V$ is linear, $\varepsilon\in B$, and $J$ is an ideal of $B$ satisfying
--   $$
--   a\in J\quad\Longleftrightarrow\quad\varepsilon a=0,
--   \qquad P(e(a))=e(\varepsilon a)
--   \quad(a\in B).
--   $$
--   Then there is a linear isomorphism
--   $$
--   \psi:B/J\xrightarrow{\sim}\operatorname{im}P
--   $$
--   whose value on a quotient class, viewed in $V$, is
--   $$
--   \psi([a])=e(\varepsilon a).
--   $$
--   In particular,
--   $$
--   \operatorname{finrank}_K(B/J)=\operatorname{finrank}_K(\operatorname{im}P).
--   $$
--   Finite-dimensionality is not required. The assertion also applies when either space is zero. Idempotence of $\varepsilon$ or $P$ is not assumed: the kernel and coordinate identities are the exact hypotheses needed.
-- source:
--   Derived linear-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. If an ideal J is the kernel of multiplication by an element epsilon and a linear equivalence identifies that multiplication with an operator P, then B/J is linearly equivalent to the range of P. The equivalence sends [a] to the coordinates of epsilon*a and preserves finrank. Uses the first isomorphism theorem and restriction of scalars in Mathlib. No new definitions or platform theorem dependencies.

import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Finrank

theorem WeierstrassEllipticZeta.multiplication_quotient_range_equivalence
    (K B V : Type*) [Field K] [CommRing B] [Algebra K B]
    [AddCommGroup V] [Module K V] (e : B ≃ₗ[K] V)
    (P : Module.End K V) (ε : B) (J : Ideal B)
    (hJ : ∀ a, a ∈ J ↔ ε * a = 0)
    (hP : ∀ a, P (e a) = e (ε * a)) :
    ∃ ψ : (B ⧸ J) ≃ₗ[K] LinearMap.range P,
      (∀ a, (ψ (Ideal.Quotient.mk J a) : V) = e (ε * a)) ∧
      Module.finrank K (B ⧸ J) = Module.finrank K (LinearMap.range P) := by sorry
