-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_candidate_locus_cost_bound
-- name    : WeierstrassEllipticZeta.finite_candidate_locus_cost_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-22T06:29:13.686808+00:00
-- url     : https://prove2.me/theorems/2e690c3c-a614-4436-9c1d-2fcd2e9fae42
-- title:
--   A.1 cost bound using finitely many locus candidates
-- statement:
--   Retain exactly the analytic, elliptic, quasiperiod and jet-stabilization
--   hypotheses of the parent A.1 frontier. Thus the entire functions $S_j$ give
--   the regularized Weierstrass coordinates, $\eta$ is the actual quasiperiod map,
--   and the function $B$ gives the stated uniform stabilization of chart jet ideals.
--
--   Prove that there is one positive real constant $C$, independent of the positive
--   integers $m,n,U$, the finite set $X$ containing zero, and the bihomogeneous
--   polynomial $Q$, with the following property. If the diagonal pullback of $Q$
--   is not identically zero but has the required chart-normalized order at least
--   $3U+1$ on $X+X+X$, then there exist:
--
--   - a candidate $k$ from the point, whole-fibre, and period-pair line candidates;
--   - a complex anchor $r$ passing the candidate's finite vanishing tests;
--   - a chart $c\in\{0,1\}$ and $z\in X+X+X$ at which that chart's denominator
--     does not vanish;
--
--   such that
--   $$
--   |X\bmod K(k)|\,E(c,z)
--   \le C\bigl(d(k,m)+1\bigr)n^2.
--   $$
--   Here $E(c,z)$ is the previously defined positive capped chart cost, using
--   cap $B(m+2n)$ and requested order parameter $U$. The candidate list has at
--   most $2+|X|(|X|-1)$ elements by the new complete theorem. Its line samples
--   follow actual period/quasiperiod displacements.
--
--   The point and whole-fibre candidates and kernels are the established ones.
--   The line candidate from $(x,y)$ uses slope $\eta(x-y)/(x-y)$.
--   The complex anchor is still unrestricted. This is the remaining geometric
--   selection and uniform cost inequality, not a completed A.1 proof.
-- source:
--   Derived finite-candidate selection for the A.1 frontier in https://prove2.me/theorems/863bfa22-6f5f-421e-ad37-5ebe13eb142a. Source motivation: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A, proof of Proposition A.1, case (4), equation (A.16): distinct representatives in one quotient class give a nonzero period. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. Together with the already formalized elementary line kernel {omega in Lambda : eta(omega)=alpha*omega}, this yields the derived slope alpha=eta(x-y)/(x-y). Root counting proves equivalence of period-scaled and canonical samples. The finite-candidate theorem is proved here without platform theorem dependencies. It is not the paper's global zero estimate. Both frontier directions preserve C, the anchor, chart point, cost and class count; a line without collisions may become a point. The anchor and global cost inequality remain Open. No numerical integer-search improvement is claimed.

import Definitions.Def_WeierstrassEllipticZeta_FiniteLocusCandidates
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

theorem WeierstrassEllipticZeta.finite_candidate_locus_cost_bound
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
        ∃ (k : FiniteLocusCandidate L.lattice X) (r : Fin 3 → ℂ),
          (∀ w ∈ candidateLocusSamples L.lattice η X k r m n,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            (((X.image (elementaryPeriodKernel L.lattice η
              (candidateLocusShape L.lattice η X k)).mkQ).card *
              cappedChartCost L S Q (B (m + 2 * n)) U c z : ℕ) : ℝ) ≤
              C * (((elementaryDegree (candidateLocusShape L.lattice η X k) m + 1) *
                n ^ 2 : ℕ) : ℝ) := by sorry
