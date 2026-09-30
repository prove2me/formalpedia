-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_line_anchor_gcd_compression
-- name    : WeierstrassEllipticZeta.line_anchor_gcd_compression
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T18:23:49.879331+00:00
-- url     : https://prove2.me/theorems/2291bcf1-9ef4-45de-bdc7-a6a691bdb425
-- title:
--   Sparse sparse line-anchor GCD certificates with degree-sensitive cardinality bound
-- statement:
--   Let Q have homogeneous bidegree (m,n) in the existing elliptic-extension coordinates. At every fixed coordinate b and slope alpha, the selected slice indices J lie in {0,...,m+n}, their GCD equals the existing line-anchor GCD G exactly, and
--
--   |J| + natDegree(G) <= n+1.
--
--   Thus |J|<=n+1 always and |J|<=n when G has positive degree, the condition for a viable line. The selected family also has minimum cardinality among all subsets of the canonical sample indices giving this same GCD. The zero-obstruction convention is included, with J empty and G zero. No positivity assumptions on m,n or analytic assumptions on S are needed.
--
--   For every predicate on the underlying finite locus candidate, existence of an old GCD-tested anchor satisfying it is equivalent to existence of a compressed-GCD anchor satisfying it. The equivalence preserves the exact candidate, coordinate b, period-pair index and point/fibre branches.
--
--   Previously the defining GCD used m+n+1 slices. It can now be represented exactly with at most n+1 slices, or at most n for a positive-degree GCD; more precisely at most n+1-deg(G). This is a bound on the size of a selected subfamily, not a claim that the first n samples suffice. The largest possible sample index remains m+n. Finding a minimum subfamily may still require the full family. The degree-n bound, integer-search bound and global geometric cost estimate are unchanged.
-- source:
--   Derived sparse-GCD criterion for the A.1 frontier https://prove2.me/theorems/aa2fcba7-944a-414e-b9df-82c4f489201c. Starting from a nonzero polynomial p_i, retain another polynomial only when it lowers the GCD degree. This gives a GCD-preserving subfamily J with |J|+deg(G)<=deg(p_i)+1. For the canonical line slices deg(p_i)<=n, hence |J|<=n+1-deg(G), and at most n for positive-degree G. The complete proof also establishes minimum cardinality and exact candidate equivalence. Primary pinned sources: Finset.gcd_insert and Finset.gcd_dvd, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GCDMonoid/Finset.lean; Polynomial.associated_of_dvd_of_natDegree_le, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean; Finset.exists_min_image, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Max.lean. This is a derived supporting theorem. Mission context: the elementary line case in Appendix A of Senthil Kumar K (2026), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The old family has m+n+1 slices. The subset depends on the polynomials; neither the maximum sample index m+n nor the integer-search bound changes. No efficient algorithm to find the subset or global geometric cost estimate is proved.

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Polynomial.Div
import Definitions.Def_WeierstrassEllipticZeta_SparseLineAnchorGCD
import Mathlib.Tactic

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.line_anchor_gcd_compression
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (∀ b α : ℂ,
      lineAnchorGCDCore S Q m n b α ⊆ Finset.range (m + n + 1) ∧
      sparseLineAnchorGCD S Q m n b α = lineAnchorGCD S Q m n b α ∧
      (lineAnchorGCDCore S Q m n b α).card +
        (lineAnchorGCD S Q m n b α).natDegree ≤ n + 1 ∧
      (0 < (lineAnchorGCD S Q m n b α).natDegree →
        (lineAnchorGCDCore S Q m n b α).card ≤ n) ∧
      (∀ J : Finset ℕ, J ⊆ Finset.range (m + n + 1) →
        J.gcd (fun j : ℕ => anchorSlice S Q b α j) = lineAnchorGCD S Q m n b α →
        (lineAnchorGCDCore S Q m n b α).card ≤ J.card)) ∧
    ∀ (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
      (K : Set ℂ) (Z : Finset ℂ) (P : FiniteLocusCandidate Λ X → Prop),
      (∃ a : GCDAnchorCandidate Λ η X S Q m n K Z,
        P (gcdAnchorLocus Λ η X S Q m n K Z a)) ↔
      (∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        P (sparseGCDAnchorLocus Λ η X S Q m n K Z a)) := by sorry
