-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_lemma1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.lemma1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:45:37.390986+00:00
-- url     : https://prove2.me/theorems/607c30ec-abae-499b-a64c-d0144e74bea0
-- title:
--   Lemma 1: finite-rank truncation
-- statement:
--   Let $P_n,Q_n$ be increasing finite-rank orthogonal projections on separable complex Hilbert spaces $H,K$, respectively, converging strongly to the identities. For a density state $\rho$, set $a_n=\operatorname{Tr}((P_n\otimes Q_n)\rho)$. There is $N$ such that $a_n>0$ for every $n\ge N$. For this tail define
--
--   $$\rho_n=a_n^{-1}(P_n\otimes Q_n)\rho(P_n\otimes Q_n).$$
--
--   Then $\mathrm{SN}(\rho_n)\to\mathrm{SN}(\rho)$ in the extended nonnegative numbers. If $\mathrm{SN}(\rho)<\infty$, then $\mathrm{SN}(\rho_n)=\mathrm{SN}(\rho)$ for all sufficiently large $n$.
--
--   This provides finite-rank approximation of Schmidt number without normalizing a zero compression.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 6, Lemma 1: finite-rank truncation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF pp.6–7, Lemma 1.
Printed: normalize each n, even when compression mass vanishes. Changed: choose
an eventually positive tail and normalize there. Strong convergence ensures this
tail, and both limiting assertions are unchanged. Zero compression is never a state. -/
theorem lemma1 {I J : Type} [Countable I] [Countable J]
    (P : ℕ → BoundedOp I I) (Q : ℕ → BoundedOp J J)
    (hP : projectionApproximation P) (hQ : projectionApproximation Q)
    (rho : State (I × J)) :
    ∃ N : ℕ, (∀ n ≥ N, 0 < compressionMass (P n) (Q n) rho) ∧
      ∃ r : ℕ → State (I × J),
        (∀ n, (r n).coefficients =
          (((compressionMass (P (n + N)) (Q (n + N)) rho)⁻¹ : ℝ) : ℂ) •
            localProjectionCompression (P (n + N)) (Q (n + N)) rho) ∧
        Tendsto (fun n => continuousSchmidtNumber (r n)) atTop (nhds (continuousSchmidtNumber rho)) ∧
        (continuousSchmidtNumber rho < ⊤ → ∃ M, ∀ n ≥ M, continuousSchmidtNumber (r n) = continuousSchmidtNumber rho) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
