-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sampled_locus_four_equation_certificate
-- name    : WeierstrassEllipticZeta.sampled_locus_four_equation_certificate
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-22T02:45:24.920918+00:00
-- url     : https://prove2.me/theorems/aae7ee1d-79e8-444d-9ac1-03a2ab38cb18
-- title:
--   A.1 multiplicity certificate using four equations
-- statement:
--   Under the same elliptic analytic hypotheses and uniform derivative-ideal cap as sampled_locus_pure_power_certificate, find a positive real C uniform in the positive degrees m,n, positive U, finite set X containing zero, and bihomogeneous polynomial Q with nonzero entire pullback and order at least 3U+1 throughout X+X+X.
--
--   Choose the same kind of elementary point, line in a fixed elliptic fibre, or whole fibre, with anchor r satisfying the prescribed finite locus-zero tests. Choose a valid chart c and a point z in X+X+X. Let E denote the canonical capped chart cost there.
--
--   Choose four polynomials b_i in C[t,x,y,u], one monomial order and four exponents d_i, with each leading coefficient a unit and each leading exponent vector equal to d_i e_i. The auxiliary ideal is now fixed to J = (b_0,b_1,b_2,b_3). In the spectrum of C[t,x,y,u]/J, choose distinct primes indexed by the classes of X modulo the elementary period kernel, each with local length at least E. Require
--
--   \[
--   \prod_{i=0}^{3} d_i \leq C(\operatorname{elementaryDegree}(\mathrm{shape},m)+1)n^2.
--   \]
--
--   This child is equivalent to the immediately preceding certificate frontier, with the same C, polynomials, exponents, monomial order, locus and chart point. The proved ideal-elimination theorem transfers any old prime family to the generated quotient without decreasing its local lower lengths. It does not prove that suitable equations or primes can be selected from the analytic input. Their construction and the uniform exponent-product bound remain Open.
-- source:
--   Derived ideal-elimination lemma for A.1 pure-power certificates. The map R/(b_i) -> R/I is surjective whenever each b_i belongs to I. Its maps on prime localizations are surjective, so local module lengths cannot increase after passing to R/I. This follows from the localization map and length APIs in pinned Mathlib: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Localization/AtPrime/Basic.lean and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Length.lean. The existing Proved pure-power bound https://prove2.me/theorems/e9388901-0807-47a0-a199-355c708a5ad9 bounds the generated quotient and its total local multiplicities by the same exponent product. The source relation is a supporting zero-dimensional ideal-monotonicity step for the global multiplicity argument of Philippon (1986), section 3, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. No full multihomogeneous Bezout result is claimed. Both frontier directions preserve C, the four polynomials, their exponents and monomial order, the locus and chart point, and all lower budgets. The auxiliary ideal and primes can change. Selecting the four equations and proving the uniform bidegree product bound remain Open.

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

theorem WeierstrassEllipticZeta.sampled_locus_four_equation_certificate
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
        ∃ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
          (∀ w ∈ elementaryLocusSamples shape r m n,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            ∃ (o : MonomialOrder.{0, 0} (Fin 4))
              (d : Fin 4 → ℕ) (b : Fin 4 → MvPolynomial (Fin 4) ℂ),
              (∀ i, IsUnit (o.leadingCoeff (b i))) ∧
              (∀ i, o.degree (b i) = Finsupp.single i (d i)) ∧
              ∃ p : (X.image (elementaryPeriodKernel L.lattice η shape).mkQ) →
                PrimeSpectrum (MvPolynomial (Fin 4) ℂ ⧸ Ideal.span (Set.range b)),
                Function.Injective p ∧
                (∀ i, cappedChartCost L S Q (B (m + 2 * n)) U c z ≤
                  (Module.length (Localization.AtPrime (p i).asIdeal)
                    (Localization.AtPrime (p i).asIdeal)).toNat) ∧
                ((∏ i, d i : ℕ) : ℝ) ≤
                  C * (((elementaryDegree shape m + 1) * n ^ 2 : ℕ) : ℝ) := by sorry
