-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_truncated_quotient_rank_budget
-- name    : WeierstrassEllipticZeta.stabilizer_truncated_quotient_rank_budget
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T05:13:20.41242+00:00
-- url     : https://prove2.me/theorems/ae8093e0-a79c-42e9-912c-c66e3407b9d3
-- title:
--   Bounded-degree quotient rank certificates for the A.1 dimension budget
-- statement:
--   Keep all hypotheses, the polynomial locus, the indexed finite-jet chart ideals, and their local-length budget conditions from the previous A.1 frontier. Replace only the final full-quotient dimension estimate by a bounded-degree rank certificate.
--
--   For every represented coset c, choose an order N_c and require
--
--   $$
--   \dim_{\mathbf C}F_{N_c}(J_c)=\dim_{\mathbf C}F_{N_c+1}(J_c),
--   $$
--
--   where F_n(J_c) is the image of degree-at-most-n polynomials in the chart quotient. The remaining uniform estimate is
--
--   $$
--   \sum_c\dim_{\mathbf C}F_{N_c}(J_c)
--   \le C\dim_{\mathbf C}S_{r,n},
--   $$
--
--   with the same stabilizer-dependent additive degree r and the same quantifiers on C as before.
--
--   The complete degree-stabilization theorem makes each certified rank equal to the full quotient dimension. Conversely, every original witness admits this certificate at N_c=dim(R/J_c)-1. Thus the child is equivalent to the original frontier with exactly the same ideals, local lengths, dimensions and C.
--
--   The child still must select suitable geometric data and prove the uniform rank budget from the analytic vanishing hypotheses. Bounded-degree subspaces do not by themselves provide such an estimate, an explicit numerical cutoff in terms of the bidegree, or an algorithm for testing ideal membership.
-- source:
--   Luca Chiantini and Juan Migliore, Almost maximal growth of the Hilbert function, Lemma 4.11, p. 20, https://academicweb.nd.edu/~jmiglior/CM2.pdf. The length-minus-one interpolation argument is formalized in affine degree-filtration form: an equality of consecutive ranks makes the earlier polynomial image invariant under multiplication by every variable and hence equal to the full quotient. Before stabilization, dimensions increase strictly from the constant class, forcing saturation by degree D-1 for a quotient of dimension D. The formal proof works over any field and includes nonradical ideals and the zero quotient; it does not formalize the source's sheaf-cohomology statement. Applied to A.1, it gives an equivalent bounded-degree rank certificate for each quotient dimension, retaining the same geometric data, local lengths and constant. The uniform rank estimate and geometric witness selection remain open.

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

theorem WeierstrassEllipticZeta.stabilizer_truncated_quotient_rank_budget
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
            ∃ N : (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z))) → ℕ,
              (∀ c, Module.finrank ℂ (quotientDegreeImage (J.ideal c) (N c)) =
                Module.finrank ℂ (quotientDegreeImage (J.ideal c) (N c + 1))) ∧
              ((∑ c, Module.finrank ℂ (quotientDegreeImage (J.ideal c) (N c)) : ℕ) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by sorry
