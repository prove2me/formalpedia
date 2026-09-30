-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_fibre_optimizer_section_cost_bound
-- name    : WeierstrassEllipticZeta.fibre_optimizer_section_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-23T02:02:32.388053+00:00
-- url     : https://prove2.me/theorems/4bbf6c32-45d9-4408-9a18-2b6ff528de77
-- title:
--   Geometric section-cost comparison after point and fibre optimization
-- statement:
--   Retain every hypothesis and quantifier of fibre_boundary_section_cost_bound, including the exact fibre list Z, the degree-4n polynomial, at most 8n+1 fibre period classes and at most 16n+4 fibre coordinates. Write N=card(X), M=(m+1)*card(X mod Lambda), E for the minimum chart cost, and W for the original minimum anchor weight.
--
--   Define the weight in the conclusion by the following explicit expression (inline in Lean, with no new definition):
--
--       N, if N<=M;
--       M, if N>M and Z is nonempty;
--       W, if N>M and Z is empty.
--
--   Prove that this weight times E is at most C*dim(V_mn), for one positive C chosen before m,n,U,X,Q,H,Z. The complete optimizer theorem proves this expression equals the original W in every case. Both connecting directions preserve C exactly.
--
--   The geometric upper bound remains Open in all cases. The complete contribution resolves the anchor-weight selection in the first two cases; it does not establish their geometric cost bound. The third case retains the original line-anchor minimization. The coordinate, period-class, section-space and integer-search bounds are unchanged.
-- source:
--   Derived optimizer lemma for Senthil Kumar K, Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This is a derived result about the formalization's existing candidate weights, not a quoted paper formula. Every elementary period kernel is contained in the lattice, so its image class count is at least the lattice class count q. Nonpoint weights are therefore at least (m+1)*q. The point has weight |X| and any available whole fibre has weight (m+1)*q. Consequently min(|X|,(m+1)*q)<=W_min; the point is optimal if |X|<=(m+1)*q, and a nonempty fibre list gives W_min=min(|X|,(m+1)*q). The global geometric estimate and all constants remain open/unchanged.

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

theorem WeierstrassEllipticZeta.fibre_optimizer_section_cost_bound
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
          ((((if X.card ≤ (m + 1) * (X.image L.lattice.mkQ).card then X.card
             else if Z.Nonempty then (m + 1) * (X.image L.lattice.mkQ).card
             else minimumAnchorWeight L.lattice η X S Q m n
            {b : ℂ | b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖} Z) *
            minimumChartCost L S Q (B (m + 2 * n)) U X : ℕ) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L m n) : ℝ)) := by sorry
