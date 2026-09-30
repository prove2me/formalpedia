-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_explicit_chart_cost_bound
-- name    : WeierstrassEllipticZeta.stabilizer_explicit_chart_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T14:22:54.511531+00:00
-- url     : https://prove2.me/theorems/a0ed8f33-29bc-4a56-9715-19981b921382
-- title:
--   Explicit bidegree bound for the A.1 canonical chart cost
-- statement:
--   Retain all analytic hypotheses, the nonempty polynomial locus W, the coset count k, the chosen chart c, and the point z in X+X+X from the canonical-cost frontier. Set r=m when every linear translation direction of W has zero additive coordinate, and r=0 otherwise. Let E(c,z) be the previously defined canonical positive chart cost.
--
--   The remaining conclusion is the explicit inequality
--
--       k*E(c,z) <= C*(r+1)*n^2,
--
--   where C>0 is uniform in m,n,U,X,Q, and all locus, chart and point conditions remain unchanged.
--
--   This is equivalent to the previous existence of a bound C*dim_C V(r,n). The proved lower bound (r+1)*(n+1)^2<=dim_C V(r,n) gives the old conclusion with the same C from this new one. Conversely, the upper bound dim_C V(r,n)<=30*(r+1)*n^2 gives the explicit inequality with constant 30*C from the old conclusion. Both directions preserve W,c,z and k*E.
--
--   The witness selection and this uniform inequality are still unproved. The statement exposes the remaining degree estimate; it does not assume it has been supplied by the section-dimension calculation.
-- source:
--   Two-sided section-dimension growth for the first Weierstrass cubic chart. This is an elementary supporting calculation for the section/Hilbert-function framework of Philippon (1986), section 3, especially Lemma 3.4, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. It is not a claimed proof of the multihomogeneous Hilbert polynomial or the global multiplicity theorem. The new lower bound constructs (m+1)*(n+1)^2 independent sections from t^a*x^b*y^epsilon*u^c with epsilon<=1 and b+c+epsilon<=n. Monicity of the cubic in y, via degree additivity, proves their independence in the quotient. The upper bound 30*(m+1)*n^2 is reused unchanged from the proved section-dimension theorem. Together they replace the section-dimension budget by an equivalent explicit (r+1)*n^2 budget, preserving witnesses and changing the converse constant from C to 30*C. The A.1 cost bound itself remains open.

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

theorem WeierstrassEllipticZeta.stabilizer_explicit_chart_cost_bound
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
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            (((X.image (fun v => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η v))).card *
              cappedChartCost L S Q (B (m + 2 * n)) U c z : ℕ) : ℝ) ≤
              C * ((((if (∀ v ∈ linearTranslationDirections W, v 0 = 0)
                then m else 0) + 1) * n ^ 2 : ℕ) : ℝ) := by sorry
