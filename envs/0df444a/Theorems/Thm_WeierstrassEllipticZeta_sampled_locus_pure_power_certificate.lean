-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sampled_locus_pure_power_certificate
-- name    : WeierstrassEllipticZeta.sampled_locus_pure_power_certificate
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T20:05:41.245786+00:00
-- url     : https://prove2.me/theorems/1bcb7b05-34b1-4a29-a294-b89d884b61c3
-- title:
--   A.1 global multiplicity via pure-power certificates
-- statement:
--   Assume the same elliptic analytic data, entire projective coordinates, period homomorphism and uniform derivative-ideal truncation bound as in sampled_elementary_locus_chart_cost_bound. We require a positive real constant C independent of the positive bidegrees m,n, positive jet parameter U, finite set X containing zero, and bihomogeneous polynomial Q. Q has nonzero entire pullback and order at least 3U+1 at every point of X+X+X in every valid projective chart.
--
--   For each such input, choose an elementary point, line in a fixed elliptic fibre, or whole fibre, with anchor r. Require the same finite locus-vanishing samples as before and a point z of X+X+X in a valid chart c.
--
--   Let E be the canonical capped chart cost at (c,z), and index labels by the distinct classes of X modulo the elementary period kernel. Construct an auxiliary ideal I in C[t,x,y,u], a monomial order, four nonnegative exponents d_i, and four polynomials b_i in I with invertible leading coefficients and pure-power leading exponent vectors d_i e_i. Construct an injective map from the labels to the prime spectrum of C[t,x,y,u]/I, with each local length at least E. Finally require
--
--   \[
--   \prod_{i=0}^{3} d_i \leq C\,(\operatorname{elementaryDegree}(\mathrm{shape},m)+1)n^2.
--   \]
--
--   This is a sufficient certificate route to the previous frontier. The new complete algebraic theorem derives quotient finiteness, finite local lengths and the cardinality-times-cost bound from this data. Constructing the data with the uniform exponent-product bound remains Open. The auxiliary ideal is not asserted to be the original derivative ideal, a cubic chart ideal, or a radical ideal. No converse equivalence or full multihomogeneous Bézout theorem is claimed.
-- source:
--   A derived sufficient algebraic certificate for the A.1 global multiplicity estimate. Mathlib's multivariate division theorem MonomialOrder.div implies that pure-power leading terms x_i^(d_i) give a spanning box of size product_i d_i in the quotient: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/MvPolynomial/Groebner.lean. Combine this with the existing Proved local multiplicity theorem https://prove2.me/theorems/5db538fd-0b38-451e-b2db-ffec33a196f1. The relation to Philippon (1986), Proposition 3.3 and section 5 (https://www.numdam.org/item/10.24033/bsmf.2060.pdf), is a restricted certificate-based route to a degree upper bound, not a formalization of his full multihomogeneous Bezout argument. The A.1 child must still construct the locus and auxiliary ideal, produce distinct local primes with the required lower lengths, and bound the exponent product uniformly in the original bidegrees. No converse or new numerical A.1 constant is claimed.

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

theorem WeierstrassEllipticZeta.sampled_locus_pure_power_certificate
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
            ∃ (I : Ideal (MvPolynomial (Fin 4) ℂ)) (o : MonomialOrder.{0, 0} (Fin 4))
              (d : Fin 4 → ℕ) (b : Fin 4 → MvPolynomial (Fin 4) ℂ),
              (∀ i, b i ∈ I) ∧
              (∀ i, IsUnit (o.leadingCoeff (b i))) ∧
              (∀ i, o.degree (b i) = Finsupp.single i (d i)) ∧
              ∃ p : (X.image (elementaryPeriodKernel L.lattice η shape).mkQ) →
                PrimeSpectrum (MvPolynomial (Fin 4) ℂ ⧸ I),
                Function.Injective p ∧
                (∀ i, cappedChartCost L S Q (B (m + 2 * n)) U c z ≤
                  (Module.length (Localization.AtPrime (p i).asIdeal)
                    (Localization.AtPrime (p i).asIdeal)).toNat) ∧
                ((∏ i, d i : ℕ) : ℝ) ≤
                  C * (((elementaryDegree shape m + 1) * n ^ 2 : ℕ) : ℝ) := by sorry
