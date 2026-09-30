-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_chart_section_dimension_budget
-- name    : WeierstrassEllipticZeta.stabilizer_chart_section_dimension_budget
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T00:14:47.965193+00:00
-- url     : https://prove2.me/theorems/e81e1754-aae9-4fce-a3f5-5e3fa5aeb763
-- title:
--   Stabilizer multiplicity budget bounded by the chart section dimension
-- statement:
--   This remaining geometric theorem keeps the original period pair, sigma data, analytic coordinates, quasiperiod map, certified cutoff B, bihomogeneous nonzero polynomial, high-order vanishing hypotheses, and capped chart-jet budgets. It must produce a nonempty polynomially constrained locus W and natural budgets e for the represented stabilizer cosets.
--
--   The requested total budget is now C times dim S_(r,n), where S is the first-chart section space and r=m when every complex linear stabilizer direction has zero first coordinate, and r=0 otherwise. The constant C is positive and independent of m,n,U,X,Q. There is no separate exponent b in this child.
--
--   The completed dimension theorem proves dim S_(r,n)<=60*profile(m)*n^2. Thus a proof of this geometric comparison gives the previous frontier with coefficient 60*C and b=2. All polynomial constraints, candidate-prime conditions, exact local lengths, and analytic assumptions are retained.
--
--   The child is a sufficient geometric route to the original zero estimate. No converse or equivalence of the full theorem statements has been formalized. The missing work is global locus and point selection, the relation between cosets and components, and a bound on total localized multiplicity by the relevant section dimension. The finite-dimensional calculation alone does not prove that comparison or A.1.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 3, pp. 362-365, section-space/Hilbert-function setup and Lemma 3.2 on primary multiplicities: https://www.numdam.org/item/10.24033/bsmf.2060.pdf. The present elementary supporting calculation uses the explicit first-chart cubic and weights 2,3,1 on x,y,u. It constructs a rectangular spanning family and proves dim S_(m,n)<=2*(m+1)*(2*n+1)*(4*n+1), hence <=30*(m+1)*n^2 for n>=1. It is not a proof of Lemma 3.2 or of the required geometric multiplicity-to-dimension comparison. The frontier reduction turns a C-times-section-dimension bound into the original numeric bound with coefficient 60*C and exponent 2. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X. Global geometric selection and the component multiplicity comparison remain Open.

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

theorem WeierstrassEllipticZeta.stabilizer_chart_section_dimension_budget
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
          ∃ e : GraphExtensionGroup L.lattice η ⧸ linearTranslationImage L.lattice η W → ℕ,
            (∀ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z)), Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U (e c) (X + X + X))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by sorry
