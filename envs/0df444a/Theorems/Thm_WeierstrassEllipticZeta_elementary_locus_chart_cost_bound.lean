-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elementary_locus_chart_cost_bound
-- name    : WeierstrassEllipticZeta.elementary_locus_chart_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T15:45:34.06939+00:00
-- url     : https://prove2.me/theorems/73f3e157-d73f-4764-92c3-4de3711838b4
-- title:
--   A.1 cost bound for elementary affine loci
-- statement:
--   Under precisely the original analytic, quasiperiod, derivative-cap, bidegree,
--   nonvanishing, and high-order hypotheses of stabilizer_explicit_chart_cost_bound,
--   choose one elementary locus: a point, an affine line of slope α in a fixed
--   elliptic fibre, or the whole affine fibre. Require Q to vanish on that locus.
--   Choose the original valid chart and point c,z in X+X+X. Prove the bound
--
--       #(X modulo K_shape) * E(c,z) ≤ C * (d_shape(m)+1) * n²,
--
--   with one uniform C>0. Here E is the unchanged canonical capped chart cost,
--   K_shape is {0}, {ω∈Λ:η(ω)=αω}, or Λ, and d_shape(m) is m, 0, or 0.
--
--   This is equivalent to the parent frontier with the same constant C. The proved
--   elementary geometry supplies the forward direction. The already-Proved
--   projection restriction and the new replacement theorem supply the full
--   converse. The chosen shape, anchor, chart point, and uniform upper bound still
--   have to be obtained from the analytic hypotheses; this child remains Open.
-- source:
--   Elementary affine locus normalization and exact period kernels in the mission's existing covering coordinates. This is a derived supporting result for the stabilizer/coset framework of Philippon (1986), section 5, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. It does not formalize the global multiplicity theorem or assert an algebraic-subgroup identification. Under the established additive/elliptic projection alternative, replace a nonempty locus by a point, a line of slope alpha in a fixed elliptic fibre, or the full fibre. The exact curve kernels are zero, the periods satisfying eta(omega)=alpha*omega, and the entire period lattice. Both the finite coset count and additive degree factor are preserved. The complete geometry proof has no platform theorem dependencies; the converse uses the already-Proved projective locus stabilizer construction. The frontier equivalence keeps C, the chart point and the local cost unchanged. The uniform cost bound and selection of its elementary witness remain open.

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

theorem WeierstrassEllipticZeta.elementary_locus_chart_cost_bound
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
          (∀ w ∈ elementaryLocus shape r,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            (((X.image (elementaryPeriodKernel L.lattice η shape).mkQ).card *
              cappedChartCost L S Q (B (m + 2 * n)) U c z : ℕ) : ℝ) ≤
              C * (((elementaryDegree shape m + 1) * n ^ 2 : ℕ) : ℝ) := by sorry
