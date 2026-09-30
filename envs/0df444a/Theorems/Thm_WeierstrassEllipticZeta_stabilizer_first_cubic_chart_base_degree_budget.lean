-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_first_cubic_chart_base_degree_budget
-- name    : WeierstrassEllipticZeta.stabilizer_first_cubic_chart_base_degree_budget
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-20T21:44:39.802883+00:00
-- url     : https://prove2.me/theorems/38213748-7dd2-4a8b-9df9-7adabe60af5f
-- title:
--   Stabilizer degree budget with the explicit first-chart cubic base
-- statement:
--   This is the remaining stabilizer degree-budget theorem with the first-chart orbit kernel replaced by its explicit cubic ideal.
--
--   Keep the original hypotheses on the period pair, normalized sigma differential data, entire projective coordinates, quasiperiod map, bidegree $(m,n)$, finite set $X$ containing zero, nonzero pullback, and order at least $3U+1$ on $X+X+X$.
--
--   One must still find a constant $C>0$ uniform in $m,n,U,X,Q$, and then a nonempty zero locus $W$, an exponent $b\le2$, and natural multiplicity budgets for the represented cosets modulo its linear-translation image. Each represented coset must have an available chart point in the triple sumset where every qualifying persistent minimal prime satisfies its localized-length bound.
--
--   The first-chart base is now explicitly
--
--   $$I_0=(y^2-4x^3+g_2x+g_3)+(Q_0).$$
--
--   The second-chart base remains its global analytic-orbit relation ideal plus normalized $Q_1$. Candidate primes are minimal over the differential prolongations at stages $iU$ and $(i+1)U$, where $i\in\{0,1,2\}$.
--
--   The original sum bound remains
--
--   $$\sum_c e_c\le C\,\begin{cases}m,&\text{all linear translation directions have zero additive coordinate},\\1,&\text{otherwise}\end{cases}n^b.$$
--
--   Only the budget data type in the original formal statement is replaced. The complete cubic-ideal theorem and a checked converse show that this replacement preserves the exact witness conditions and lengths. Locus and point selection, the geometric relation between cosets and components, and the uniform total-length degree estimate remain obligations. Second-chart identification and chart gluing remain to be supplied if needed for that argument.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, pp. 380-382: ambient algebraic-group ideals in the global zero-estimate argument. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. The new proof identifies the first affine chart orbit ideal exactly with the principal Weierstrass cubic ideal, by polynomial normal form, period/quasiperiod saturation, parity and the infinite regular wp image. It replaces that chart's base by the cubic plus normalized Q. Second-chart ideal identification, chart gluing, locus and coset/component selection, and the uniform total-degree estimate remain open.

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

theorem WeierstrassEllipticZeta.stabilizer_first_cubic_chart_base_degree_budget
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
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
        ∃ (W : Set (Fin 3 → ℂ)) (b : ℕ), W.Nonempty ∧
          (∀ w ∈ W,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          b ≤ 2 ∧
          ∃ e : GraphExtensionGroup L.lattice η ⧸ linearTranslationImage L.lattice η W → ℕ,
            (∀ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z)), Nonempty (FirstCubicChartBaseBudget L S Q U (e c) (X + X + X))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by sorry
