-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_punctual_chart_ideals
-- name    : WeierstrassEllipticZeta.stabilizer_punctual_chart_ideals
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T02:52:55.813885+00:00
-- url     : https://prove2.me/theorems/201e9208-0881-4018-ae45-9468beeffb04
-- title:
--   Point-supported chart ideals with a uniform total dimension budget
-- statement:
--   Keep the parent theorem's period pair, sigma differential data, entire projective coordinates, quasi-period map, and certified derivative-order cutoff. There is a positive constant, independent of the polynomial, bidegrees, order and finite set, with the following property.
--
--   For positive bidegrees and order parameter, a finite set containing zero, and an eligible bihomogeneous polynomial whose entire pullback is nonzero and whose normalized pullbacks have order at least three times the parameter plus one on the triple sumset,
--
--   $$m,n,U\ge1,\qquad 0\in X,\qquad
--   \operatorname{ord}_v(Q_{\rm normalized})\ge3U+1\quad(v\in X+X+X),$$
--
--   construct the same nonempty polynomial-constrained locus as in the parent. Index the required data by the cosets represented by the finite set in the quotient by this locus's canonical linear translation stabilizer.
--
--   For each label, construct a distinct point in the first Weierstrass chart and an ideal supported exactly at that point, containing the cubic relation:
--
--   $$R=\mathbb C[t,x,y,u],\qquad F=y^2-4x^3+g_2x+g_3,$$
--
--   $$F\in I_c,\qquad V_{\mathbb C}(I_c)=\{a_c\},\qquad c\longmapsto a_c\text{ injective}.$$
--
--   The localized length of each ideal at its support point must bound the corresponding capped chart-jet budget. The sum of the full quotient dimensions must satisfy
--
--   $$\sum_c\dim_{\mathbb C}(R/I_c)\le C\dim_{\mathbb C}S_{r,n},\qquad
--   r=\begin{cases}m,&\text{all translation directions have zero additive coordinate},\\0,&\text{otherwise}.\end{cases}$$
--
--   The ideals may be nonradical. Their finite-dimensionality follows from their single-point support. The gluing theorem builds the parent's global ideal by intersection and preserves every local budget, with quotient dimension exactly the sum displayed above. Conversely, extraction from any parent witness preserves the selected localizations and does not increase the total dimension, so a checked converse keeps the same constant.
--
--   Selection of the locus, points and point-supported ideals from the analytic vanishing data, the chart-budget comparisons, and the uniform sum bound remain open. No correspondence between these support points and the separately selected analytic chart-jet points is silently added.
-- source:
--   Stacks Project, Chinese remainder theorem, Lemma 10.15.4, https://stacks.math.columbia.edu/tag/00DT; Artinian local decomposition, Lemma 10.53.6, https://stacks.math.columbia.edu/tag/00JB; nilpotence of the radical, Lemma 10.53.4, https://stacks.math.columbia.edu/tag/00J8. The proof uses the already proved finite-zero-set criterion to pass between point-supported polynomial ideals and finite-dimensional coordinate algebras. Pairwise distinct support points make the ideals comaximal. Their intersection retains every selected localization, has exactly the selected zero set, and has quotient dimension equal to the sum of component dimensions. Conversely, from a finite quotient and selected zeros, construct I + m_i^(N_i) using nilpotence in the local quotient. This preserves each selected localization and the total component dimension is at most the original dimension. Application to A.1: construction of the global chart quotient is reduced equivalently to individual point-supported chart ideals with the same local multiplicity budgets and a bound on their total dimensions. The same uniform constant is retained. Neither selection of those ideals from the analytic vanishing data nor the uniform geometric dimension estimate is claimed.

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

theorem WeierstrassEllipticZeta.stabilizer_punctual_chart_ideals
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
          ∃ J : PunctualChartIdealData L
            (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z))),
            (∀ c, Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U
              (J.localLength c) (X + X + X))) ∧
            ((∑ c, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal c) : ℕ) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by sorry
