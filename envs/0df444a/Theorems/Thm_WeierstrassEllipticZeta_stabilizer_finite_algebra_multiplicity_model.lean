-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_stabilizer_finite_algebra_multiplicity_model
-- name    : WeierstrassEllipticZeta.stabilizer_finite_algebra_multiplicity_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-21T00:36:51.328261+00:00
-- url     : https://prove2.me/theorems/f8f79782-22bf-41a1-a6f5-d82625e0a5a1
-- title:
--   Finite algebra realizing the stabilizer multiplicity budgets
-- statement:
--   Retain the period lattice $L$, elliptic sigma differential data $D$, five entire projective coordinate functions $S_j$, their stated formulas and nonvanishing, the quasiperiod map $\eta$, and the certified derivative cutoff $B$ from the parent theorem.
--
--   The assertion is that there is a positive real constant $C$, independent of $m,n,U,X,Q$, with the following property. Let $m,n,U\geq1$, let $X\subset\mathbb C$ be finite with $0\in X$, and let $Q$ be bihomogeneous of bidegree $(m,n)$. Suppose its restriction to the analytic curve is not identically zero and every defined normalized coordinate representative vanishes to order at least $3U+1$ on $X+X+X$.
--
--   There must exist a nonempty locus $W\subset\mathbb C^3$ on which the translated projective evaluation of $Q$ vanishes. Let $H_W$ be the image, in the period graph quotient, of the complex linear translation directions preserving $W$. Let $Y$ be the finite set of cosets represented by the curve points associated to $X$. There must also exist a finite-dimensional commutative complex algebra $A$ and an injective map
--
--   $$p:Y\longrightarrow\operatorname{Spec}(A).$$
--
--   At each represented coset, the local length
--
--   $$e_c=\ell_{A_{p(c)}}(A_{p(c)})$$
--
--   must satisfy the parent's capped chart-jet budget: some point in $X+X+X$ and one of the two charts has nonzero chart denominator, and every eligible prime persisting in two successive capped derivative blocks has localized quotient length at most $e_c$.
--
--   Finally, write $r=m$ if every linear translation direction of $W$ has zero first coordinate, and $r=0$ otherwise. If $S_{r,n}$ is the first-chart section space, require
--
--   $$\dim_{\mathbb C}A\leq C\dim_{\mathbb C}S_{r,n}.$$
--
--   This is a sufficient finite-algebra realization of the parent's total multiplicity comparison. Selecting $W$, constructing $A$ and the distinct support primes, relating their local lengths to the chart budgets, and proving the uniform dimension bound remain substantive requirements. The assertion does not claim that the original positive-dimensional chart ring is finite-dimensional. No converse to this sufficient formulation is asserted.
-- source:
--   Stacks Project, Lemma 10.53.5 (tag 00JA) and Lemma 10.53.6 (tag 00JB), https://stacks.math.columbia.edu/tag/00JA and https://stacks.math.columbia.edu/tag/00JB: Artinian decomposition into prime localizations; Lemma 10.52.3 (tag 00IV), https://stacks.math.columbia.edu/tag/00IV: additivity of module length. For a finite algebra over an algebraically closed field, the residue fields have degree one, so the local lengths sum exactly to the vector-space dimension. An injectively indexed subfamily has no greater sum. This is the finite-algebra, dimension-zero supporting case of the multiplicity relation in Philippon (1986), section 3, Lemma 3.2, p. 364, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. The frontier child asks for a finite complex algebra realizing the chart multiplicity budgets at distinct primes, with its dimension bounded by the relevant section-space dimension. This is a sufficient finite-model route, not a quotation or proof of the full Lemma 3.2. Locus selection, finite-algebra realization, local-length comparisons and the uniform section-degree bound remain required. Application: Senthil Kumar K (2026), Appendix A, Theorem A.2, https://doi.org/10.1017/S001309152610145X.

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

theorem WeierstrassEllipticZeta.stabilizer_finite_algebra_multiplicity_model
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
          ∃ M : FiniteAlgebraMultiplicityModel
            (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z))),
            (∀ c, Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U
              (M.localLength c) (X + X + X))) ∧
            (Module.finrank ℂ M.A : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by sorry
