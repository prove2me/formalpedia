-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_line_anchor_gcd_criterion
-- name    : WeierstrassEllipticZeta.line_anchor_gcd_criterion
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T17:14:15.24448+00:00
-- url     : https://prove2.me/theorems/7c1f7cae-c753-4895-b9b5-95f7cf7c55af
-- title:
--   Exact GCD criterion for finite line intercepts
-- statement:
--   Let S be any five complex-valued functions and let Q be a bihomogeneous polynomial of bidegree (m,n). At each elliptic coordinate b and slope alpha, form the lineAnchorGCD defined from the canonical intercept slices, with the existing zero-obstruction convention.
--
--   The theorem proves all of the following:
--
--   - The existing finite set of tested line intercepts equals the set of distinct roots of lineAnchorGCD.
--   - The natural degree of lineAnchorGCD is at most n.
--   - A valid tested line intercept exists if and only if the natural degree of lineAnchorGCD is positive.
--
--   Moreover, fix any lattice submodule, quasiperiod linear map, finite input set X, coordinate region K, finite fibre list Z and predicate P on the underlying point/fibre/period-pair locus candidates. A fibre-enumerated anchor satisfying P exists if and only if a GCD anchor satisfying P exists. The latter keeps the same point and fibre branches and replaces a line's intercept witness by the positive-degree GCD condition at its slope and coordinate.
--
--   The equivalence preserves the exact underlying finite locus candidate, including its period-pair index. It therefore preserves any shape, degree or quotient-class condition on that candidate. No analyticity, compactness, positivity of the bidegrees or nonempty input set is needed. The theorem does not bound the number of possible line coordinates, construct a numerical root-finding algorithm, or prove the global A.1 cost estimate.
-- source:
--   Derived GCD criterion for line anchors in the A.1 frontier https://prove2.me/theorems/0d893d2a-f5ba-4f36-a984-39565ad59d87. For fixed b and slope alpha, take the GCD of the intercept slices F(j,b,alpha*j+beta), j=0,...,m+n, with the existing zero-obstruction case assigned zero. The exact tested intercept set equals its distinct root set. The GCD divides the nonzero obstruction, so its degree is at most n. The fundamental theorem of algebra makes positive degree equivalent to existence of a tested intercept. Primary pinned sources: Finset.dvd_gcd_iff and Finset.gcd_dvd, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GCDMonoid/Finset.lean; Polynomial.mem_roots and Polynomial.card_roots', https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean; and Complex.exists_root, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/Polynomial/Basic.lean. The cost frontier replaces its chosen intercept by the positive-degree test, preserving the exact candidate, coordinate, class count, degree, chart point, chart cost and C. This is a derived supporting criterion. Mission context: the elementary line case in Appendix A of Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. Line coordinates remain potentially continuous. The existing degree-n bound and integer-search bound are unchanged; the global geometric cost estimate remains Open. No numerical root-finding algorithm is claimed.

import Definitions.Def_WeierstrassEllipticZeta_LineAnchorGCD
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.line_anchor_gcd_criterion
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (∀ b α : ℂ,
      lineAnchorRoots S Q m n b α = (lineAnchorGCD S Q m n b α).roots.toFinset ∧
      (lineAnchorGCD S Q m n b α).natDegree ≤ n ∧
      ((lineAnchorRoots S Q m n b α).Nonempty ↔
        0 < (lineAnchorGCD S Q m n b α).natDegree)) ∧
    ∀ (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
      (K : Set ℂ) (Z : Finset ℂ) (P : FiniteLocusCandidate Λ X → Prop),
      (∃ a : FibreEnumeratedAnchorCandidate Λ η X S Q m n K Z,
        P (fibreEnumeratedAnchorLocus Λ η X S Q m n K Z a)) ↔
      (∃ a : GCDAnchorCandidate Λ η X S Q m n K Z,
        P (gcdAnchorLocus Λ η X S Q m n K Z a)) := by sorry
