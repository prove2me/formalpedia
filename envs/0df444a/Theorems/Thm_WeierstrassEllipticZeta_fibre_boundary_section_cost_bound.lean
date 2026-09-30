-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_fibre_boundary_section_cost_bound
-- name    : WeierstrassEllipticZeta.fibre_boundary_section_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-23T01:26:18.247704+00:00
-- url     : https://prove2.me/theorems/a6bf4412-d57e-4be4-b2e6-cdf0dd179991
-- title:
--   Geometric section-cost comparison with at most 16n+4 fibre coordinates
-- statement:
--   The same A.1 geometric section-cost comparison as fibre_count_section_cost_bound, with the supplied coordinate bound tightened from Z.card<=32*n+4 to Z.card<=16*n+4.
--
--   Every other hypothesis and quantifier is retained: the period pair, entire sigma coordinates, quasiperiod map, uniform jet cap, positive degrees, high contact on the triple sumset, the nonzero degree-4n polynomial and its root certificate, and the exact fibre list in the closed anchor region. The bound of 8n+1 on its period classes is unchanged.
--
--   The conclusion remains W_min*E_min <= C*dim(V_mn), with one positive C chosen before all degree and finite-set data. The new coordinate bound follows from a complete theorem; it is not an additional unproved restriction. The parent sketch and checked converse preserve C exactly.
--
--   This remains an Open geometric multiplicity comparison. The improved fibre count does not supply a bound on local multiplicities or resolve the line-anchor alternatives.
-- source:
--   Derived boundary-count refinement for Senthil Kumar K, Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. These constants are derived here, not quoted from the paper. Every nonzero lattice class has at most two representatives in a closed two-dimensional basis parallelepiped; only the zero class can have four. Thus card(Z)<=2*card(Z/Lambda)+2. Combined with the proved polynomial root class count, this improves the coordinate bound from 8*deg(H)+4 to 4*deg(H)+4, and the A.1 fibre bound from 32n+4 to 16n+4. The 8n+1 period-class bound and geometric constant C are unchanged.

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

theorem WeierstrassEllipticZeta.fibre_boundary_section_cost_bound
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
        ∀ H : Polynomial ℂ, H ≠ 0 → H.natDegree ≤ 4 * n →
          H.roots.toFinset.card ≤ 4 * n →
          (∀ b : ℂ, b ∉ L.lattice → () ∈ fibreAnchorChoices S Q m n b →
            L.weierstrassP b ∈ H.roots.toFinset) →
        ∀ Z : Finset ℂ,
          (∀ b : ℂ, b ∈ Z ↔
            (b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖) ∧
              () ∈ fibreAnchorChoices S Q m n b) →
          (L.lattice.mkQ '' (Z : Set ℂ)).ncard ≤ 8 * n + 1 →
          Z.card ≤ 16 * n + 4 →
          (((minimumAnchorWeight L.lattice η X S Q m n
            {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z *
            minimumChartCost L S Q (B (m + 2 * n)) U X : ℕ) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L m n) : ℝ)) := by sorry
