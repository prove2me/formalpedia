-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sampled_locus_canonical_equation_bound
-- name    : WeierstrassEllipticZeta.sampled_locus_canonical_equation_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-22T05:57:02.44645+00:00
-- url     : https://prove2.me/theorems/863bfa22-6f5f-421e-ad37-5ebe13eb142a
-- title:
--   A.1 degree bound for canonical multiplicity equations
-- statement:
--   Retain the analytic hypotheses and uniform derivative-ideal cap of the preceding quotient-degree certificate frontier. Seek a positive constant $C$ uniform in positive $m,n,U$, a finite $X$ containing zero, and a bihomogeneous $Q$ with nonzero entire pullback and order at least $3U+1$ throughout $X+X+X$.
--
--   Choose an elementary point, line in a fixed elliptic fibre, or entire fibre, with an anchor satisfying the prescribed finite zero tests. Choose a valid chart $c$ and $z\in X+X+X$. Let $E$ be the canonical capped chart cost there, and let $k$ be the number of classes of $X$ modulo the elementary period kernel. Both $k$ and $E$ are positive under these inputs.
--
--   The four equations are now prescribed:
--
--   $$F(t)=\prod_{j=0}^{k-1}(t-j)^E,\qquad x,\qquad y,\qquad u.$$
--
--   The formal product indexes the quotient classes and numbers them by their finite-type equivalence with $0,\ldots,k-1$. Prove
--
--   $$\dim_{\mathbb C}\mathbb C[t,x,y,u]/(F(t),x,y,u)
--   \leq C(\operatorname{elementaryDegree}(\mathrm{shape},m)+1)n^2.$$
--
--   The new Proved construction supplies the leading powers, finite quotient and distinct primes with local length exactly $E$; its dimension is exactly $kE$. No equations, monomial order, exponent family or prime family remain to be selected in this child.
--
--   This statement is equivalent to the preceding certificate frontier with the same $C$, locus and chart point. Replacing an old certificate by this one can only decrease its dimension. The bound on $kE$ and the geometric witness selection remain unproved; no smaller numerical constant is asserted.
-- source:
--   Derived explicit length-profile realization for the A.1 certificate in https://prove2.me/theorems/049daeec-3df5-4ef0-9a62-8ff9030ce7f4. Take F(t)=product_i(t-a_i)^(e_i) and J=(F,x,y,u). The unit pure leading powers and the Proved standard-monomial theorem https://prove2.me/theorems/59cb8f12-d4f7-4f7f-ba02-e645e5402da4 give dimension sum_i e_i. Projections onto C[T]/(T^(e_i)) give the local lower lengths; the finite-algebra length sum forces equality. Background: Stacks Project, Lemma 10.53.6, tag 00JB, https://stacks.math.columbia.edu/tag/00JB, Artinian decomposition into prime localizations. The univariate quotient dimension is pinned Mathlib's finrank_quotient_span_eq_natDegree in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean. This is a supporting algebraic construction, not Philippon's global zero estimate. Both frontier directions preserve C, the locus and chart point. Equations and primes become prescribed by the label count and cost; the global inequality and geometric selection remain Open.

import Mathlib.RingTheory.MvPolynomial.Groebner
import Definitions.Def_WeierstrassEllipticZeta_ElementaryLocusSamples
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

theorem WeierstrassEllipticZeta.sampled_locus_canonical_equation_bound
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
          (∀ w ∈ elementaryLocusSamples shape r m n,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            let ι : Type := (X.image (elementaryPeriodKernel L.lattice η shape).mkQ)
            let e := cappedChartCost L S Q (B (m + 2 * n)) U c z
            let b : Fin 4 → MvPolynomial (Fin 4) ℂ :=
              ![∏ i : ι, (MvPolynomial.X 0 -
                MvPolynomial.C (((Fintype.equivFin ι i).val : ℕ) : ℂ)) ^ e,
                MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3]
            ((Module.finrank ℂ
              (MvPolynomial (Fin 4) ℂ ⧸ Ideal.span (Set.range b)) : ℕ) : ℝ) ≤
              C * (((elementaryDegree shape m + 1) * n ^ 2 : ℕ) : ℝ) := by sorry
