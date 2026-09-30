-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_fibre_enumerated_locus_cost_bound
-- name    : WeierstrassEllipticZeta.fibre_enumerated_locus_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-22T16:22:11.178847+00:00
-- url     : https://prove2.me/theorems/0d893d2a-f5ba-4f36-a984-39565ad59d87
-- title:
--   A.1 cost bound with whole-fibre coordinates enumerated
-- statement:
--   This is the remaining A.1 geometric cost bound after enumerating all possible whole-fibre coordinates in the bounded period region.
--
--   Retain exactly the analytic hypotheses, true quasiperiod map and stabilizing chart-cap function B from bounded_anchor_locus_cost_bound. There must be one positive real constant C valid for all positive m,n,U, all finite X containing zero and all eligible bihomogeneous Q. The diagonal pullback is assumed nonzero, and every valid normalized pullback has analytic order at least 3U+1 at each point of X+X+X.
--
--   Let K be the set of b in the closed period parallelogram with norm(b)<=norm(omega_1)+norm(omega_2). For any finite list Z consisting exactly of the b in K passing the whole-fibre tests, choose a fibre-enumerated anchor candidate a, a chart index c and a point z in X+X+X with nonzero chart denominator. Prove the unchanged inequality k*E<=C*(d(m)+1)*n^2, where k is the number of X-classes modulo the candidate period kernel, E is the canonical capped chart cost, and d(m) is the existing shape-dependent degree parameter.
--
--   The complete finite-fibre theorem proves that such a list Z exists. The point branch has no free coordinate; the whole-fibre branch chooses b from Z; the line branch still chooses b in K and an intercept among its tested roots. The statement quantifies over every exact enumeration Z, rather than requiring the solver to construct one. A checked full converse proves equivalence with the parent, preserving C, chart point, chart cost, exact candidate, class count and degree. The global geometric bound remains Open, and no bound on the size of Z is assumed or supplied.
-- source:
--   Derived finite whole-fibre enumeration for the A.1 frontier https://prove2.me/theorems/cd5e1c96-23d5-494e-ba7b-70a81e2a670c. For a nonzero diagonal pullback, one of the (m+1)(n+1) integer fibre sample functions b -> F(i,b,j) is nonzero. Otherwise the Proved finite interpolation theorem 0d85f1e1-6c11-46f4-8278-88c0ac3aa265 would force every fibre, and hence the diagonal, to vanish. That sample function is entire. Every whole-fibre coordinate is among its zeros, of which only finitely many lie in a compact region. Primary analytic sources: pinned Mathlib's AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/IsolatedZeros.lean, and IsCompact.finite_sdiff_of_mem_codiscreteWithin, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/DiscreteSubset.lean. The new finite list replaces the whole-fibre coordinate in an exact candidate model; line coordinates still range over the compact region. Both frontier directions preserve the exact finite locus candidate, class count, degree, chart point, chart cost and C. Mission context: the regularized exponential map at the beginning of Appendix A in Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This enumeration is derived here, not quoted as the paper's global zero estimate. No cardinality bound in terms of m,n or root-isolation algorithm is proved. The global uniform cost estimate remains Open; the integer-search bound is unchanged.

import Definitions.Def_WeierstrassEllipticZeta_FibreEnumeratedAnchors
import Mathlib.Algebra.Module.ZLattice.Basic
import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
import Definitions.Def_WeierstrassEllipticZeta_FiniteLocusCandidates
import Mathlib.RingTheory.MvPolynomial.Groebner
import Definitions.Def_WeierstrassEllipticZeta_ElementaryLocusSamples
import Definitions.Def_WeierstrassEllipticZeta_ElementaryLoci
import Definitions.Def_WeierstrassEllipticZeta_CanonicalChartCost
import Definitions.Def_WeierstrassEllipticZeta_SectionJetEvaluation
import Definitions.Def_TranscendenceTheory_PolynomialQuotientDegreeFiltration
import Definitions.Def_WeierstrassEllipticZeta_FiniteJetChartIdeals
import Definitions.Def_WeierstrassEllipticZeta_PunctualChartIdeals
import Definitions.Def_WeierstrassEllipticZeta_FiniteChartZeroLocus
import Definitions.Def_WeierstrassEllipticZeta_ChartQuotientMultiplicity
import Definitions.Def_TranscendenceTheory_FiniteAlgebraMultiplicityModel
import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Definitions.Def_WeierstrassEllipticZeta_CappedChartJets
import Definitions.Def_WeierstrassEllipticZeta_FiniteChartJets
import Definitions.Def_WeierstrassEllipticZeta_CubicChartBase
import Definitions.Def_WeierstrassEllipticZeta_FirstCubicChartBase
import Definitions.Def_WeierstrassEllipticZeta_GlobalChartBase
import Definitions.Def_WeierstrassEllipticZeta_ChartOrbitBase
import Definitions.Def_WeierstrassEllipticZeta_ChartSelectionData
import Definitions.Def_WeierstrassEllipticZeta_ChartProlongationData
import Definitions.Def_WeierstrassEllipticZeta_ChartPrimeMultiplicityData
import Definitions.Def_TranscendenceTheory_AnalyticOrbitMultiplicityData
import Definitions.Def_TranscendenceTheory_MinimalPrimeMultiplicityData
import Definitions.Def_TranscendenceTheory_IsolatedComponentMultiplicityData
import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData
import Definitions.Def_TranscendenceTheory_DifferentialMultiplicity
import Definitions.Def_TranscendenceTheory_LinearTranslationStabilizer
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise
open TranscendenceTheory

open scoped Classical

theorem WeierstrassEllipticZeta.fibre_enumerated_locus_cost_bound
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    (B : ℕ → ℕ)
    (hB : ∀ (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ),
      (∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n) →
      ∀ (c : Fin 2) (T : ℕ), extensionChartJetIdeal L Q c T =
        extensionChartJetIdeal L Q c (min T (B (m + 2 * n)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v) →
        ∀ Z : Finset ℂ,
          (∀ b : ℂ, b ∈ Z ↔
            (b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖) ∧
              () ∈ fibreAnchorChoices S Q m n b) →
          ∃ a : FibreEnumeratedAnchorCandidate L.lattice η X S Q m n
            {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z,
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            (((X.image (elementaryPeriodKernel L.lattice η
              (candidateLocusShape L.lattice η X
                (fibreEnumeratedAnchorLocus L.lattice η X S Q m n
                  {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z a))).mkQ).card *
              cappedChartCost L S Q (B (m + 2 * n)) U c z : ℕ) : ℝ) ≤
              C * (((elementaryDegree (candidateLocusShape L.lattice η X
                (fibreEnumeratedAnchorLocus L.lattice η X S Q m n
                  {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z a)) m + 1) *
                n ^ 2 : ℕ) : ℝ) := by sorry
