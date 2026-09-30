-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_positive_length_budget
-- name    : WeierstrassEllipticZeta.stabilizer_positive_length_budget
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T09:40:01.896377+00:00
-- url     : https://prove2.me/theorems/148a7cf3-dc1c-4d5d-9ee9-1435e1c24e6e
-- title:
--   Positive local-length budget for the A.1 multiplicity estimate
-- statement:
--   Retain all analytic hypotheses of the section-evaluation rank frontier and its nonempty polynomial locus W. For each translation-coset label c, choose a positive integer e_c and a capped chart-jet budget with upper bound e_c. Require the sum of e_c to be at most C times the original first-chart section-space dimension, with additive degree m or zero according to the same stabilizer condition and elliptic degree n. The same C>0 must work uniformly in m,n,U,X,Q.
--
--   There is no auxiliary polynomial-ideal selection in this remaining statement. The complete curvilinear realization theorem constructs such ideals from any positive e_c with exactly those local lengths and quotient dimensions. The proved interpolation theorem identifies their simultaneous section rank with the sum of their dimensions. Conversely, the old ideal witnesses supply e_c as their local lengths, which are positive and equal the corresponding dimensions. Hence the new statement is equivalent with the same W, chart budgets and C.
--
--   The unresolved geometric and quantitative work is choosing W and budgets satisfying the original analytic conditions and the uniform sum bound. The auxiliary support points used in realization need not be analytic chart points; this is consistent with the existing frontier's exact hypotheses.
-- source:
--   Explicit curvilinear length realization for the current A.1 interface. The model is C[T]/(T^e), with basis 1,T,...,T^(e-1), embedded along the additive coordinate of the cubic chart at (a,0,b,0), b^2=-g3. Length comparison and localization use the composition-series principles in Stacks Project, Section 10.52, Lemmas 10.52.5, 10.52.6 and 10.52.11, https://stacks.math.columbia.edu/tag/00IU. This is a derived auxiliary construction, not a theorem quoted from Kumar's Appendix A. Every prescribed positive length is realized exactly, and the existing frontier reduces equivalently to a uniform sum of positive chart budgets. The locus and constant are preserved; no identification of these auxiliary ideals with derivative ideals or analytic support points is asserted. The geometric selection and uniform bound remain open.

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

theorem WeierstrassEllipticZeta.stabilizer_positive_length_budget
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
          ∃ e : (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z))) → ℕ,
            (∀ c, 0 < e c) ∧
            (∀ c, Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U
              (e c) (X + X + X))) ∧
            ((∑ c, e c : ℕ) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by sorry
