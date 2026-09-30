-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_anchor_locus_cost_bound
-- name    : WeierstrassEllipticZeta.finite_anchor_locus_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-22T06:56:20.220923+00:00
-- url     : https://prove2.me/theorems/5c0ca929-d071-43e0-996d-dfa3194114a0
-- title:
--   A.1 cost bound using finite anchors at one elliptic coordinate
-- statement:
--   Keep exactly the parent's elliptic, analytic, quasiperiod, nonvanishing and
--   uniform jet-stabilization hypotheses. Prove that one positive real constant
--   $C$ works for every positive $m,n,U$, finite $X$ containing zero, and
--   bihomogeneous polynomial $Q$ satisfying the parent's diagonal nonvanishing
--   and order-at-least-$3U+1$ hypotheses on $X+X+X$.
--
--   The required conclusion is the existence of an elliptic coordinate
--   $b\in\mathbb C$, a member $a$ of the finite anchor candidate family at $b$,
--   and a chart $c\in\{0,1\}$ with a point $z\in X+X+X$ whose chart denominator
--   does not vanish, such that
--   $$
--   |X\bmod K(a)|\,E(c,z)
--   \le C\bigl(d(a,m)+1\bigr)n^2.
--   $$
--   The cost $E(c,z)$ is the existing capped chart cost with cap $B(m+2n)$
--   and order parameter $U$.
--
--   At each $b$, the candidate family has at most $2+n|X|(|X|-1)$ members.
--   Its point anchor is the origin; its whole-fibre anchor is $(0,b,0)$; its
--   line anchors are $(0,b,\beta)$ for the tested roots of the fixed obstruction
--   polynomial and period-pair slopes. No additional vanishing-test obligation is
--   needed: the complete theorem proves it for every candidate, using origin
--   vanishing derived from the original high-order assumptions.
--
--   The elliptic coordinate $b$ remains unrestricted, and the displayed uniform
--   cost inequality remains the main unresolved obligation. Finiteness at each
--   $b$ is not a finite search over all complex elliptic coordinates.
-- source:
--   Derived finite-anchor reduction for the A.1 frontier https://prove2.me/theorems/2e690c3c-a614-4436-9c1d-2fcd2e9fae42. For a fixed elliptic coordinate b and slope alpha, form the univariate intercept slices F(j,b,alpha*j+beta), j=0,...,m. Each has degree at most n. The first nonzero slice has at most n roots. If every slice is zero, degree-m interpolation in the additive coordinate proves whole-fibre vanishing. The finite-anchor theorem and the frontier converse are derived here; they are not a theorem quoted from the mission paper. Primary root-counting reference: pinned Mathlib, Polynomial.card_roots' and Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A, Proposition A.1 case (4), surrounding (A.16), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. At each b there are at most 2+n*|X|*(|X|-1) tested candidates. The origin point, normalized fibre anchor, and line roots remove free additive and vertical anchor coordinates. The elliptic coordinate b and uniform geometric cost estimate remain Open. The constant and degree parameter are preserved, while class count can decrease. No integer-search bound improvement or numerical root-finding algorithm is claimed.

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

theorem WeierstrassEllipticZeta.finite_anchor_locus_cost_bound
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
        ∃ (b : ℂ) (a : FiniteAnchorCandidate L.lattice η X S Q m n b),
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            (((X.image (elementaryPeriodKernel L.lattice η
              (candidateLocusShape L.lattice η X
                (anchorCandidateLocus L.lattice η X S Q m n b a))).mkQ).card *
              cappedChartCost L S Q (B (m + 2 * n)) U c z : ℕ) : ℝ) ≤
              C * (((elementaryDegree (candidateLocusShape L.lattice η X
                (anchorCandidateLocus L.lattice η X S Q m n b a)) m + 1) *
                n ^ 2 : ℕ) : ℝ) := by sorry
