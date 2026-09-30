-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_anchor_candidate_selection
-- name    : WeierstrassEllipticZeta.finite_anchor_candidate_selection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T06:56:14.107417+00:00
-- url     : https://prove2.me/theorems/a8f601c6-867b-4589-84b7-6ca3e5c72d95
-- title:
--   Finite anchor candidates from at most n intercept roots
-- statement:
--   Let $\Lambda\subseteq\mathbb C$ be a $\mathbb Z$-submodule, let
--   $\eta:\Lambda\to\mathbb C$ be $\mathbb Z$-linear, and let $X$ be finite.
--   Let $Q$ have bidegree $(m,n)$ in the established two-plus-five coordinates,
--   and let $S_0,\ldots,S_4$ be arbitrary complex functions. Set
--   $$
--   F_Q(t,b,u)=Q(1,t,S_0(b),S_1(b),S_2(b),
--   S_3(b)+uS_0(b),S_4(b)+uS_2(b)).
--   $$
--   Assume $F_Q(0,0,0)=0$.
--
--   For every fixed elliptic coordinate $b$, there is the explicitly defined
--   finite anchor candidate family: the origin point; the whole fibre with
--   anchor $(0,b,0)$ if its finite tests pass; and period-pair lines with normalized
--   anchor $(0,b,\beta)$, where $\beta$ belongs to the tested root set of the
--   first nonzero integer intercept slice. The family has cardinality at most
--   $$2+n|X|(|X|-1).$$
--   Every member passes the previous frontier's period-scaled vanishing tests.
--
--   Furthermore, any previous finite locus candidate and arbitrary anchor which
--   pass those tests can be replaced by a member of this family at some $b$.
--   The quotient class count does not increase, and the degree parameter is
--   exactly preserved:
--   $$
--   |X\bmod K_{\rm new}|\le |X\bmod K_{\rm old}|,\qquad
--   d_{\rm new}(m)=d_{\rm old}(m).
--   $$
--
--   For a line of slope $\alpha$, normalize its anchor $r$ to
--   $(0,r_1,r_2-\alpha r_0)$. A nonzero slice has degree at most $n$, so the
--   intercept belongs to a set of at most $n$ roots. If all $m+1$ integer slices
--   are zero, interpolation proves vanishing of the whole fibre, which may
--   replace the line and decrease the quotient class count. A point may be
--   replaced by the origin using the stated hypothesis.
--
--   The result includes empty $X$, zero degrees and identically zero fibre
--   restrictions. It removes the unrestricted additive and vertical anchor
--   coordinates. It does not choose $b$ or prove the global A.1 cost inequality.
-- source:
--   Derived finite-anchor reduction for the A.1 frontier https://prove2.me/theorems/2e690c3c-a614-4436-9c1d-2fcd2e9fae42. For a fixed elliptic coordinate b and slope alpha, form the univariate intercept slices F(j,b,alpha*j+beta), j=0,...,m. Each has degree at most n. The first nonzero slice has at most n roots. If every slice is zero, degree-m interpolation in the additive coordinate proves whole-fibre vanishing. The finite-anchor theorem and the frontier converse are derived here; they are not a theorem quoted from the mission paper. Primary root-counting reference: pinned Mathlib, Polynomial.card_roots' and Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A, Proposition A.1 case (4), surrounding (A.16), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. At each b there are at most 2+n*|X|*(|X|-1) tested candidates. The origin point, normalized fibre anchor, and line roots remove free additive and vertical anchor coordinates. The elliptic coordinate b and uniform geometric cost estimate remain Open. The constant and degree parameter are preserved, while class count can decrease. No integer-search bound improvement or numerical root-finding algorithm is claimed.

import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
import Mathlib.Tactic

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.finite_anchor_candidate_selection
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hzero : MvPolynomial.eval ![1, 0, S 0 0, S 1 0, S 2 0, S 3 0, S 4 0] Q = 0) :
    (∀ b : ℂ,
      Fintype.card (FiniteAnchorCandidate Λ η X S Q m n b) ≤
        2 + X.card * (X.card - 1) * n ∧
      ∀ a : FiniteAnchorCandidate Λ η X S Q m n b,
        ∀ w ∈ candidateLocusSamples Λ η X (anchorCandidateLocus Λ η X S Q m n b a)
            (anchorCandidatePoint Λ η X S Q m n b a) m n,
          MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
            S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
    (∀ (k : FiniteLocusCandidate Λ X) (r : Fin 3 → ℂ),
      (∀ w ∈ candidateLocusSamples Λ η X k r m n,
        MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
          S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) →
      ∃ (b : ℂ) (a : FiniteAnchorCandidate Λ η X S Q m n b),
        (X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X
          (anchorCandidateLocus Λ η X S Q m n b a))).mkQ).card ≤
          (X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X k)).mkQ).card ∧
        elementaryDegree (candidateLocusShape Λ η X
          (anchorCandidateLocus Λ η X S Q m n b a)) m =
          elementaryDegree (candidateLocusShape Λ η X k) m) := by sorry
