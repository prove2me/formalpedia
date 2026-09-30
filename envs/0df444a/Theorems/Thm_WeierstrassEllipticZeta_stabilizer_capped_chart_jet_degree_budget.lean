-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_capped_chart_jet_degree_budget
-- name    : WeierstrassEllipticZeta.stabilizer_capped_chart_jet_degree_budget
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-20T23:42:43.952444+00:00
-- url     : https://prove2.me/theorems/f6b31fa8-82d8-415d-bc46-f147aa9dfad7
-- title:
--   Stabilizer degree budget with a certified degree-dependent jet cap
-- statement:
--   This is the remaining stabilizer degree-budget theorem, using capped chart-jet ideals. In addition to the original hypotheses it receives a function B and an explicit certificate that, for every eligible Q of bidegree (m,n), chart c and order T, the original jet ideal equals the ideal at min(T,B(m+2n)). The completed supporting theorem proves the existence of such a B, even positive and monotone.
--
--   The conclusion retains the same constant C, nonempty polynomially constrained locus W, exponent b<=2, natural budgets indexed by represented stabilizer cosets, and original sum inequality. Only FiniteChartJetBudget is replaced by CappedChartJetBudget at cap B(m+2n). The constant is still outside all quantifiers over m,n,U,X,Q. For any valid supplied cap, the old and new budget witnesses are equivalent and preserve exact localized lengths.
--
--   The capped generating family has a bound independent of derivative order. The remaining challenge is quantitative growth in the two degrees, together with the global locus/point selection and relation between cosets and components. The Noetherian cutoff has no established numerical value or growth rate. This child still requires the same A.1 degree budget; it is not discharged by finiteness alone.
-- source:
--   Supporting Noetherian specialization lemma for the A.1 formalization. Mathlib, RingTheory/Noetherian/Defs.lean, monotone_stabilizes_iff_noetherian: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Defs.html#monotone_stabilizes_iff_noetherian. Universal coefficient variables make ideal stabilization uniform over all polynomials of bounded degree; specialization preserves exact ideal membership and yields J_T=J_min(T,B(m+2*n)) in both charts. B is positive and monotone, but no numerical value or growth bound is proved. Philippon (1986), Bull. Soc. Math. France 114, 355-383, section 5, pp. 380-382, https://www.numdam.org/item/10.24033/bsmf.2060.pdf, provides the broader derivative/translation-ideal framework. This is not that paper's quantitative zero estimate. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X. The uniform A.1 degree budget and global geometric selection remain Open.

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

theorem WeierstrassEllipticZeta.stabilizer_capped_chart_jet_degree_budget
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
        ∃ (W : Set (Fin 3 → ℂ)) (b : ℕ), W.Nonempty ∧
          (∀ w ∈ W,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          b ≤ 2 ∧
          ∃ e : GraphExtensionGroup L.lattice η ⧸ linearTranslationImage L.lattice η W → ℕ,
            (∀ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z)), Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U (e c) (X + X + X))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by sorry
