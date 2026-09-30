-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_bounded_anchor_locus_cost_bound
-- name    : WeierstrassEllipticZeta.bounded_anchor_locus_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-22T15:03:18.812075+00:00
-- url     : https://prove2.me/theorems/cd5e1c96-23d5-494e-ba7b-70a81e2a670c
-- title:
--   A.1 finite-anchor cost bound in the compact period parallelogram
-- statement:
--   This is the remaining A.1 finite-anchor cost bound with its elliptic coordinate restricted to a fixed compact period parallelogram.
--
--   Keep exactly the hypotheses of finite_anchor_locus_cost_bound: a period pair and sigma differential data, entire regularized projective coordinates agreeing with their elliptic expressions off the lattice and never simultaneously zero, the actual quasiperiod map, and a cap B that stabilizes every chart jet ideal. There is a positive real constant C such that the following holds for all positive m,n,U, every finite X containing zero and every bihomogeneous Q of bidegree (m,n). Assume the diagonal pullback is nonzero and its normalized analytic order is at least 3U+1 at every point of X+X+X in every valid projective chart.
--
--   Choose b in the closed parallelogram spanned by omega_1 and omega_2, satisfying norm(b) <= norm(omega_1)+norm(omega_2), a finite anchor candidate a at b, and a chart index c and point z in X+X+X with nonzero chart denominator. Prove that the number k of X-classes modulo the candidate's elementary period kernel times the canonical capped chart cost E is at most C*(d(m)+1)*n^2, where d(m) is the existing elementary degree for the candidate's shape.
--
--   The sole change from the parent is the parallelogram and norm restriction on b. Every analytic hypothesis, quantifier order, chart cost, degree parameter and numerical constant is retained. A checked period-normalization converse proves that these restrictions preserve all witnesses needed for the parent estimate with the same C, class count and cost. They do not supply a candidate satisfying the estimate: that uniform geometric bound remains the open obligation.
-- source:
--   Derived compact period normalization for the A.1 frontier https://prove2.me/theorems/5c0ca929-d071-43e0-996d-dfa3194114a0. Primary analytic source: the period/quasiperiod law and exponential map at the beginning of Appendix A in Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The Proved projective descent theorem ec2a2e1c-5f8f-4ae2-bb23-b71a175888c7 gives invariance of bihomogeneous vanishing under (b,u) -> (b-omega,u+eta(omega)), including lattice points. Canonical finite tests and line-root membership are preserved by this transport. Primary lattice reference: pinned Mathlib ZSpan.fract_mem_fundamentalDomain, ZSpan.fundamentalDomain_subset_parallelepiped and ZSpan.norm_fract_le, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Module/ZLattice/Basic.lean. Set omega=floor(b); the new b lies in the closed compact period parallelogram and has norm at most norm(omega_1)+norm(omega_2). The finite-anchor theorem and exact frontier equivalence are derived here, not quoted as the paper's zero estimate. The exact locus candidate, class count, degree parameter, chart cost and C are preserved. The coordinate b still ranges over a continuum; the global uniform cost estimate remains Open and the integer-search bound is unchanged.

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

theorem WeierstrassEllipticZeta.bounded_anchor_locus_cost_bound
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
        ∃ b : ℂ, b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ ∧
          ∃ a : FiniteAnchorCandidate L.lattice η X S Q m n b,
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            (((X.image (elementaryPeriodKernel L.lattice η
              (candidateLocusShape L.lattice η X
                (anchorCandidateLocus L.lattice η X S Q m n b a))).mkQ).card *
              cappedChartCost L S Q (B (m + 2 * n)) U c z : ℕ) : ℝ) ≤
              C * (((elementaryDegree (candidateLocusShape L.lattice η X
                (anchorCandidateLocus L.lattice η X S Q m n b a)) m + 1) *
                n ^ 2 : ℕ) : ℝ) := by sorry
