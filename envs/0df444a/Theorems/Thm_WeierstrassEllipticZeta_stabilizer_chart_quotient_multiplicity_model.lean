-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_chart_quotient_multiplicity_model
-- name    : WeierstrassEllipticZeta.stabilizer_chart_quotient_multiplicity_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T01:06:40.219384+00:00
-- url     : https://prove2.me/theorems/4c53fae1-0d6a-412b-b6b9-40d6955ad53f
-- title:
--   Finite chart quotient realizing the stabilizer multiplicity budgets
-- statement:
--   Keep the period pair $L$, sigma differential data $D$, entire projective coordinate functions $S_j$, coordinate identities and nonvanishing, quasiperiod map $\eta$, and certified derivative cutoff $B$ from the parent theorem.
--
--   There must be a positive real constant $C$, independent of $m,n,U,X,Q$, with the following property. Let $m,n,U\geq1$, let $X\subset\mathbb C$ be finite with $0\in X$, and let $Q$ be bihomogeneous of bidegree $(m,n)$. Its restriction to the analytic curve must not be identically zero, and every defined normalized coordinate representative must vanish to order at least $3U+1$ on $X+X+X$.
--
--   As in the parent, select a nonempty locus $W\subset\mathbb C^3$ on which the translated projective evaluation of $Q$ vanishes. Let $H_W$ be the image of its complex linear translation directions in the period graph quotient, and let $Y$ be the cosets represented by the curve points associated to $X$.
--
--   In the first chart's polynomial ring
--
--   $$R=\mathbb C[t,x,y,u],\qquad F_L=y^2-4x^3+g_2x+g_3,$$
--
--   select an ideal $I$ containing $F_L$, with $R/I$ finite-dimensional, and distinct prime ideals $p(c)\supseteq I$ indexed by $c\in Y$. Define
--
--   $$e_c=\ell_{R_{p(c)}}\bigl(R_{p(c)}/IR_{p(c)}\bigr).$$
--
--   Each $e_c$ must satisfy the existing capped chart-jet budget: at an appropriate point of $X+X+X$ with nonzero denominator in one of the two charts, every eligible prime persisting in two successive capped derivative blocks has localized quotient length at most $e_c$.
--
--   Put $r=m$ if every linear translation direction of $W$ has zero first coordinate, and $r=0$ otherwise. Require the uniform bound
--
--   $$\dim_{\mathbb C}(R/I)\leq C\dim_{\mathbb C}S_{r,n},$$
--
--   where $S_{r,n}$ is the previously defined first-chart section space.
--
--   This is a sufficient first-chart finite-quotient route to the parent theorem. Selecting $W$, $I$, and the support primes, proving finite-dimensionality, comparing the chart budgets, and obtaining the uniform section bound remain open. The support primes are auxiliary primes labelled by the represented cosets; no unproved identification with analytic chart points is built into the data. No converse to this sufficient formulation is asserted.
-- source:
--   Stacks Project, Proposition 10.9.14 (tag 00CT), https://stacks.math.columbia.edu/tag/00CT: localization commutes with quotient; Lemma 10.52.3 (tag 00IV), https://stacks.math.columbia.edu/tag/00IV: length additivity; the quotient ideal correspondence preserves submodule lattices and module length under surjective scalar restriction. Given a finite complex quotient R/I and distinct support primes p_i containing I, the complete theorem constructs the finite algebra model A=R/I, preserves finrank exactly, and identifies each localization length with length over R_(p_i) of R_(p_i)/IR_(p_i). The new geometric child specializes R to C[t,x,y,u], requires I to contain the first Weierstrass cubic, and retains the chart-budget and uniform section-dimension obligations. It is a sufficient first-chart finite-quotient route, not a formalized converse or a claim that slicing has been constructed. Multiplicities in the source zero-estimate framework: Philippon (1986), section 3, Lemma 3.2, p. 364, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X.

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

theorem WeierstrassEllipticZeta.stabilizer_chart_quotient_multiplicity_model
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
          ∃ J : ChartQuotientMultiplicityData L
            (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z))),
            (∀ c, Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U
              (J.localLength c) (X + X + X))) ∧
            (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by sorry
