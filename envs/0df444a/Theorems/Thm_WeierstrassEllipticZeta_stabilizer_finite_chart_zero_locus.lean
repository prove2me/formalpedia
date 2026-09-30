-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_finite_chart_zero_locus
-- name    : WeierstrassEllipticZeta.stabilizer_finite_chart_zero_locus
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T01:49:49.872732+00:00
-- url     : https://prove2.me/theorems/f1961896-ea34-4355-8941-6aa5c9fa45e1
-- title:
--   Finite chart zero set realizing the stabilizer multiplicity budgets
-- statement:
--   This is the remaining geometric construction in the A.1 first-chart multiplicity argument. Retain the period pair, sigma differential data, entire homogeneous coordinate system, quasi-period map, and certified degree-dependent derivative cutoff from the parent theorem.
--
--   There is a positive constant, independent of all polynomial degrees, vanishing orders, finite sets and polynomials, with the following property. Given positive bidegrees and order parameter, a finite set containing zero, and a bihomogeneous polynomial with nonzero entire pullback whose normalized pullbacks have order at least three times the parameter plus one on the triple sumset,
--
--   $$m,n,U\ge1,\qquad 0\in X,\qquad
--   \operatorname{ord}_v(Q_{\mathrm{normalized}})\ge3U+1\quad(v\in X+X+X),$$
--
--   one must construct a nonempty locus satisfying the original polynomial constraint. For its canonical linear translation stabilizer, let the finite index set consist of the cosets represented by the given finite set.
--
--   One must then construct an ideal in the first chart ring with finite complex zero set, together with pairwise distinct zeros labelled by those represented cosets:
--
--   $$R=\mathbb C[t,x,y,u],\qquad
--    y^2-4x^3+g_2x+g_3\in I,\qquad |V_{\mathbb C}(I)|<\infty.$$
--
--   For every label, its localized quotient length must bound a capped chart-jet budget. The quotient dimension must satisfy the uniform section bound:
--
--   $$\dim_{\mathbb C}(R/I)\le C\dim_{\mathbb C}S_{r,n},\qquad
--   r=\begin{cases}m,&\text{all translation directions have zero additive coordinate},\\0,&\text{otherwise}.\end{cases}$$
--
--   The finite-zero-set theorem establishes that the quotient dimension is finite and constructs the support primes canonically from the labelled points. The ideal is not assumed radical. The labels need not exhaust its zeros; no identification between these support points and the independently selected analytic chart-jet points is assumed. The same ideal, constant and local lengths occur in the parent. A checked local converse reconstructs these geometric data from every parent quotient witness.
--
--   The locus, ideal, labelled points, finiteness of the zero set, chart-budget comparisons and uniform dimension bound remain the content of this open theorem.
-- source:
--   Stacks Project, Theorem 10.34.1 (Hilbert Nullstellensatz), https://stacks.math.columbia.edu/tag/00FV; Lemma 10.36.5 (finite type and integral imply finite), https://stacks.math.columbia.edu/tag/02JJ; section 10.53, https://stacks.math.columbia.edu/tag/00J4 (finite-dimensional algebras are Artinian, with finitely many primes, all maximal). The complete theorem proves, for any ideal in finitely many variables over an algebraically closed field, that its full coordinate quotient is finite-dimensional iff its zero set is finite. It also identifies the support primes with unique evaluation points. The ideal need not be radical. Application to the first Weierstrass chart in Senthil Kumar's A.1 multiplicity frontier: replace finite-dimensional quotient data and support primes by a finite zero set and distinct labelled chart points, preserving the ideal, local lengths, dimension and uniform constant exactly. A checked local converse shows this replacement is equivalent. This does not construct the geometric ideal from the high-order vanishing hypotheses or prove the uniform section-dimension bound.

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

theorem WeierstrassEllipticZeta.stabilizer_finite_chart_zero_locus
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
          ∃ J : FiniteChartZeroLocusData L
            (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z))),
            (∀ c, Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U
              (J.localLength c) (X + X + X))) ∧
            (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by sorry
