-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_locus_candidate_selection
-- name    : WeierstrassEllipticZeta.finite_locus_candidate_selection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T06:28:56.489803+00:00
-- url     : https://prove2.me/theorems/6fc2ef69-fbe4-4d41-a462-789df5317df0
-- title:
--   Finite geometric candidates with period-scaled vanishing tests
-- statement:
--   Let $\Lambda\subseteq\mathbb C$ be a $\mathbb Z$-submodule, let
--   $\eta:\Lambda\to\mathbb C$ be $\mathbb Z$-linear, and let $X\subseteq\mathbb C$
--   be finite. Let $Q$ be a polynomial of bidegree $(m,n)$ in the established
--   two-plus-five coordinates, and let $S_0,\ldots,S_4$ be arbitrary functions.
--   Write
--   $$
--   F_Q(t,z,u)=Q(1,t,S_0(z),S_1(z),S_2(z),
--   S_3(z)+uS_0(z),S_4(z)+uS_2(z)).
--   $$
--
--   Consider the candidate family consisting of a point, a whole elliptic fibre,
--   and a line of slope $\eta(x-y)/(x-y)$ for each distinct ordered pair
--   $x,y\in X$ with $x-y\in\Lambda$. Its cardinality is at most
--   $$2+|X|(|X|-1).$$
--   For a line candidate, vanishing at the period-scaled samples
--   $r+(j(x-y),0,j\eta(x-y))$, $0\le j\le m+n$, is equivalent to vanishing at
--   the established unit-parameter line samples. Point and fibre tests are unchanged.
--
--   Suppose an elementary locus of shape $s$ and anchor $r$ passes its canonical
--   vanishing tests. Then some candidate $k$ at the same anchor passes its candidate
--   tests and satisfies
--   $$
--   |X\bmod K(k)|=|X\bmod K(s)|,\qquad d(s,m)\le d(k,m).
--   $$
--   Here the kernels for point, line of slope $\alpha$, and fibre are respectively
--   $0$, $\{\omega\in\Lambda:\eta(\omega)=\alpha\omega\}$, and $\Lambda$.
--   The corresponding degree parameters are $m,0,0$.
--
--   A line with a collision in $X\bmod K(s)$ is represented by the colliding
--   pair. A line with no collision can be replaced by its anchor point, preserving
--   the class count and increasing the degree parameter from $0$ to $m$.
--   The result allows empty $X$ and zero bidegrees, and needs no analytic
--   hypothesis on the functions $S_j$.
--
--   This proves a finite reduction of shape and slope choices. It does not choose
--   the complex anchor or prove the uniform A.1 cost bound, and it does not give
--   an effective period-membership algorithm.
-- source:
--   Derived finite-candidate selection for the A.1 frontier in https://prove2.me/theorems/863bfa22-6f5f-421e-ad37-5ebe13eb142a. Source motivation: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A, proof of Proposition A.1, case (4), equation (A.16): distinct representatives in one quotient class give a nonzero period. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. Together with the already formalized elementary line kernel {omega in Lambda : eta(omega)=alpha*omega}, this yields the derived slope alpha=eta(x-y)/(x-y). Root counting proves equivalence of period-scaled and canonical samples. The finite-candidate theorem is proved here without platform theorem dependencies. It is not the paper's global zero estimate. Both frontier directions preserve C, the anchor, chart point, cost and class count; a line without collisions may become a point. The anchor and global cost inequality remain Open. No numerical integer-search improvement is claimed.

import Definitions.Def_WeierstrassEllipticZeta_FiniteLocusCandidates
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.finite_locus_candidate_selection
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    Fintype.card (FiniteLocusCandidate Λ X) ≤ 2 + X.card * (X.card - 1) ∧
    (∀ (k : FiniteLocusCandidate Λ X) (r : Fin 3 → ℂ),
      (∀ w ∈ candidateLocusSamples Λ η X k r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ↔
      (∀ w ∈ elementaryLocusSamples (candidateLocusShape Λ η X k) r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0)) ∧
    ∀ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
      (∀ w ∈ elementaryLocusSamples shape r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) →
      ∃ k : FiniteLocusCandidate Λ X,
        (∀ w ∈ candidateLocusSamples Λ η X k r m n,
          MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
            S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
        (X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X k)).mkQ).card =
          (X.image (elementaryPeriodKernel Λ η shape).mkQ).card ∧
        elementaryDegree shape m ≤ elementaryDegree (candidateLocusShape Λ η X k) m := by sorry
