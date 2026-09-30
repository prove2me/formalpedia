-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_minimum_cost_section_dimension_bound
-- name    : WeierstrassEllipticZeta.minimum_cost_section_dimension_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-22T19:31:10.801948+00:00
-- url     : https://prove2.me/theorems/b36f983b-aa58-4642-a9a3-5a0d99c64458
-- title:
--   A.1 minimum-cost budget in terms of actual section dimension
-- statement:
--   Retain exactly the hypotheses and quantifier order of the minimum-weight/chart-cost frontier, including its analytic sigma lift, quasiperiod data, jet-stabilization cap, bihomogeneous nonzero section, high-order vanishing on the triple sumset, and exact finite fibre list. Prove that a uniform positive constant $C$ satisfies
--
--   $$W_{\min}E_{\min}\le C\,\dim_{\mathbb C}V_{m,n},$$
--
--   where $W_{\min}$ is the minimum anchor weight, $E_{\min}$ is the minimum canonical capped chart cost, and $V_{m,n}$ is the actual first-chart section space of bidegree $(m,n)$. The cost still uses the original cap $B(m+2n)$ and order parameter $U$.
--
--   This is the remaining geometric cost comparison. The new dimension theorem implies the preceding frontier with constant $7C$. Conversely, the preceding frontier implies this one with the same constant because $(m+1)n^2\le\dim V_{m,n}$. Thus the uniform-existence statements are equivalent, although the forward conversion rescales the constant. The dimension estimate alone does not prove this cost comparison.
-- source:
--   Derived quantitative refinement of WeierstrassEllipticZeta.elliptic_first_chart_section_dimension, https://prove2.me/theorems/13b6bf3d-1364-403b-8b54-d9e68f950754. Existing normalization uses the cubic relation y^2=4*x^3-g2*x-g3 and substitutes (1,t;1,x,y,u,y*u+2*x^2). Retaining the fibre exponent c<=n and the coupled weight 2*a+3*b+c<=4*n, b<2, gives exactly (m+1)*sum(c=0..n)(4*n-c)=(7/2)*(m+1)*n*(n+1) spanning monomials for n>=1. Thus the previously Proved uniform coefficient 30 is replaced by 7. The lower bound (m+1)*(n+1)^2 is reused from the Proved section-growth theorem https://prove2.me/theorems/af52a388-2af4-4817-ace8-f041f281a3c2. Pinned arithmetic source: Finset.sum_range_id_mul_two, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Intervals.lean. Source context for the projective coordinates: Senthil Kumar K (2026), Appendix A.2, exponential mapping and the chart display preceding Lemma A.1, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This sharper dimension estimate is derived here, not quoted as a theorem of that paper. Frontier https://prove2.me/theorems/2cdf9a4f-11a1-457e-a98e-81ce6ee0b5e8 is reduced to the actual section-dimension budget W_min*E_min<=C*dim V_(m,n). That budget implies the parent with constant 7*C; the checked converse retains the parent constant using the existing lower dimension bound. The global geometric comparison remains unproved, and the integer-search bound is unchanged.

import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Definitions.Def_WeierstrassEllipticZeta_MinimumChartCost
import Definitions.Def_WeierstrassEllipticZeta_OptimalAnchorWeight
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

theorem WeierstrassEllipticZeta.minimum_cost_section_dimension_bound
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
          (((minimumAnchorWeight L.lattice η X S Q m n
            {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z *
            minimumChartCost L S Q (B (m + 2 * n)) U X : ℕ) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L m n) : ℝ)) := by sorry
