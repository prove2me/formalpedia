-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_fibre_anchor_enumeration
-- name    : WeierstrassEllipticZeta.finite_fibre_anchor_enumeration
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T16:21:59.226147+00:00
-- url     : https://prove2.me/theorems/807d1fcb-9d58-41b0-8cdf-f1716a649620
-- title:
--   Finite enumeration of whole-fibre anchors in a compact region
-- statement:
--   Let S be five entire complex functions, Q a bihomogeneous polynomial of bidegree (m,n), and suppose the diagonal pullback Q(1,z;S0(z),S1(z),S2(z),S3(z),S4(z)) is not identically zero. Let K be any compact subset of C containing zero. Fix also an arbitrary lattice submodule, quasiperiod linear map and finite input set X for the existing candidate definitions.
--
--   There is a finite set Z consisting exactly of those b in K for which the canonical whole-fibre vanishing tests pass. For every finite set Z satisfying that exact membership condition, and every predicate P on the finite point/fibre/period-pair locus candidates, the following are equivalent:
--
--   - There exist b in K and an old finite anchor candidate at b whose underlying locus candidate satisfies P.
--   - There exists a fibre-enumerated anchor candidate built from K and Z whose underlying locus candidate satisfies P.
--
--   The point is represented without a redundant b coordinate. The whole-fibre branch chooses its coordinate from the finite set Z. The line branch retains its coordinate in K and its tested finite intercept roots. The equivalence preserves the exact underlying finite locus candidate; hence it preserves its period kernel, class count and degree parameter.
--
--   The theorem allows zero bidegrees and an empty X. No elliptic differential or period assumptions on S are needed beyond entire analyticity and the stated diagonal nonvanishing. The finite list is obtained noncomputably; neither a root-isolation algorithm nor a cardinality bound depending only on m,n is claimed. Line coordinates and the A.1 geometric cost estimate remain unresolved.
-- source:
--   Derived finite whole-fibre enumeration for the A.1 frontier https://prove2.me/theorems/cd5e1c96-23d5-494e-ba7b-70a81e2a670c. For a nonzero diagonal pullback, one of the (m+1)(n+1) integer fibre sample functions b -> F(i,b,j) is nonzero. Otherwise the Proved finite interpolation theorem 0d85f1e1-6c11-46f4-8278-88c0ac3aa265 would force every fibre, and hence the diagonal, to vanish. That sample function is entire. Every whole-fibre coordinate is among its zeros, of which only finitely many lie in a compact region. Primary analytic sources: pinned Mathlib's AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/IsolatedZeros.lean, and IsCompact.finite_sdiff_of_mem_codiscreteWithin, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/DiscreteSubset.lean. The new finite list replaces the whole-fibre coordinate in an exact candidate model; line coordinates still range over the compact region. Both frontier directions preserve the exact finite locus candidate, class count, degree, chart point, chart cost and C. Mission context: the regularized exponential map at the beginning of Appendix A in Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This enumeration is derived here, not quoted as the paper's global zero estimate. No cardinality bound in terms of m,n or root-isolation algorithm is proved. The global uniform cost estimate remains Open; the integer-search bound is unchanged.

import Definitions.Def_WeierstrassEllipticZeta_FibreEnumeratedAnchors
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic

noncomputable section
open scoped Classical Topology
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.finite_fibre_anchor_enumeration
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => MvPolynomial.eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) (h0 : (0 : ℂ) ∈ K) :
    (∃ Z : Finset ℂ, ∀ b : ℂ,
      b ∈ Z ↔ b ∈ K ∧ () ∈ fibreAnchorChoices S Q m n b) ∧
    ∀ Z : Finset ℂ,
      (∀ b : ℂ, b ∈ Z ↔ b ∈ K ∧ () ∈ fibreAnchorChoices S Q m n b) →
      ∀ P : FiniteLocusCandidate Λ X → Prop,
        (∃ b : ℂ, b ∈ K ∧ ∃ a : FiniteAnchorCandidate Λ η X S Q m n b,
          P (anchorCandidateLocus Λ η X S Q m n b a)) ↔
        (∃ a : FibreEnumeratedAnchorCandidate Λ η X S Q m n K Z,
          P (fibreEnumeratedAnchorLocus Λ η X S Q m n K Z a)) := by sorry
