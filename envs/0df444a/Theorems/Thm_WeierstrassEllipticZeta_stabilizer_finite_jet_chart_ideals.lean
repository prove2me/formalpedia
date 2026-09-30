-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_finite_jet_chart_ideals
-- name    : WeierstrassEllipticZeta.stabilizer_finite_jet_chart_ideals
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T04:26:49.251385+00:00
-- url     : https://prove2.me/theorems/7e3a60d0-2a5f-4326-9684-26a15caef207
-- title:
--   Finite-jet chart ideals with the A.1 uniform dimension budget
-- statement:
--   Under the unchanged analytic, bidegree, nonvanishing, high-order vanishing, and derivative-truncation assumptions of the punctual-chart-ideal frontier, construct a nonempty polynomial locus and a family of finite-jet chart ideals indexed by the represented stabilizer cosets.
--
--   For each ideal J_c with assigned point x_c and quotient dimension d_c, the new data requires the explicit algebraic conditions
--
--   $$
--   \mathfrak m_{x_c}^{d_c}\subseteq J_c\subseteq\mathfrak m_{x_c}.
--   $$
--
--   The chart cubic belongs to every ideal, the support points are distinct, and the same local lengths must furnish the capped chart-jet budgets. The remaining quantitative requirement is unchanged:
--
--   $$
--   \sum_c d_c\le C\dim_{\mathbf C}S_{r,n},
--   $$
--
--   where r is selected from m and 0 by the original stabilizer projection condition. The constant C must be uniform in the polynomial, finite set, bidegree and vanishing order.
--
--   The proved finite-jet characterization and a checked converse identify this child exactly with the previous frontier, preserving each ideal and the same constant. This child remains responsible for selecting the locus and ideals from the analytic vanishing data, satisfying the local budget conditions, and proving the uniform sum bound. The explicit finite-jet description alone supplies none of those existence or global estimates.
-- source:
--   Stacks Project, Artinian radical nilpotence, Lemma 10.53.4, https://stacks.math.columbia.edu/tag/00J8; Hilbert Nullstellensatz, https://stacks.math.columbia.edu/tag/00FV. In a finite-dimensional algebra A, nonzero powers of a nilpotent ideal strictly decrease in dimension, so its dim(A)-th power vanishes. Applied to the quotient R/I, this proves radical(I)^dim(R/I) <= I. For polynomial ideals with singleton zero set {x}, this yields the exact finite-jet criterion m_x^d <= I <= m_x with d=dim(R/I), and reconstruction of I from its image in the finite jet algebra. The A.1 application gives an equivalent finite-jet formulation of the punctual-chart frontier, retaining the same ideals, lengths, dimensions and uniform constant. Witness selection and the geometric sum-of-dimensions bound remain open; no bidegree or integer-search bound is improved.

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

theorem WeierstrassEllipticZeta.stabilizer_finite_jet_chart_ideals
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
        ∃ W : Set (Fin 3 → ℂ), W.Nonempty ∧
          (∀ w ∈ W,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ J : FiniteJetChartIdealData L
            (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z))),
            (∀ c, Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U
              (J.localLength c) (X + X + X))) ∧
            ((∑ c, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal c) : ℕ) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by sorry
