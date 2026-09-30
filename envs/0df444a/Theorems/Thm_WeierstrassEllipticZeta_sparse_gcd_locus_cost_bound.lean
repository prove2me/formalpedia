-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sparse_gcd_locus_cost_bound
-- name    : WeierstrassEllipticZeta.sparse_gcd_locus_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-22T18:23:51.520305+00:00
-- url     : https://prove2.me/theorems/7e7bb591-b0c3-4c9f-a487-565853b9f422
-- title:
--   A.1 cost bound using compressed line-GCD certificates
-- statement:
--   This is the exact previous A.1 GCD-tested locus cost frontier with the line condition evaluated using the minimum-cardinality GCD-preserving slice subfamily. All analytic hypotheses, the exact finite whole-fibre list Z, the compact coordinate region, period-pair candidates, class counts, chart data, degree factors, positive uniform constant C and cost inequality are retained.
--
--   The companion complete theorem proves that the compressed and full GCDs are equal and that the selected slice family has size at most n+1-deg(G), hence at most n for a viable line. It also proves exact candidate equivalence. Both directions of the full frontier are checked locally with the same C, coordinate, candidate, chart point and cost.
--
--   The remaining obligation is still to choose a candidate and valid chart point whose class count k and canonical chart cost E satisfy k*E<=C*(d(m)+1)*n^2, with C independent of the finite input, polynomial and degrees. The compression does not prove this geometric estimate. Line coordinates may still vary continuously; the supplied fibre list has no degree-based size bound. The integer-search bound is unchanged.
-- source:
--   Derived sparse-GCD criterion for the A.1 frontier https://prove2.me/theorems/aa2fcba7-944a-414e-b9df-82c4f489201c. Starting from a nonzero polynomial p_i, retain another polynomial only when it lowers the GCD degree. This gives a GCD-preserving subfamily J with |J|+deg(G)<=deg(p_i)+1. For the canonical line slices deg(p_i)<=n, hence |J|<=n+1-deg(G), and at most n for positive-degree G. The complete proof also establishes minimum cardinality and exact candidate equivalence. Primary pinned sources: Finset.gcd_insert and Finset.gcd_dvd, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GCDMonoid/Finset.lean; Polynomial.associated_of_dvd_of_natDegree_le, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean; Finset.exists_min_image, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Max.lean. This is a derived supporting theorem. Mission context: the elementary line case in Appendix A of Senthil Kumar K (2026), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The old family has m+n+1 slices. The subset depends on the polynomials; neither the maximum sample index m+n nor the integer-search bound changes. No efficient algorithm to find the subset or global geometric cost estimate is proved.

import Definitions.Def_WeierstrassEllipticZeta_SparseLineAnchorGCD
import Definitions.Def_WeierstrassEllipticZeta_LineAnchorGCD
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

theorem WeierstrassEllipticZeta.sparse_gcd_locus_cost_bound
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
          ∃ a : SparseGCDAnchorCandidate L.lattice η X S Q m n
            {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z,
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            (((X.image (elementaryPeriodKernel L.lattice η
              (candidateLocusShape L.lattice η X
                (sparseGCDAnchorLocus L.lattice η X S Q m n
                  {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z a))).mkQ).card *
              cappedChartCost L S Q (B (m + 2 * n)) U c z : ℕ) : ℝ) ≤
              C * (((elementaryDegree (candidateLocusShape L.lattice η X
                (sparseGCDAnchorLocus L.lattice η X S Q m n
                  {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z a)) m + 1) *
                n ^ 2 : ℕ) : ℝ) := by sorry
