-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_corollary3_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.corollary3_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:34:22.480059+00:00
-- url     : https://prove2.me/theorems/e2283912-794b-48f3-9556-1c14fcd07db4
-- title:
--   Universal law on extensions of a fixed marginal
-- statement:
--   Let $D,E$ be nonzero finite-dimensional complex Hilbert spaces and let $\sigma_D\ge0$. Set $d=(\dim D)(\dim E)^2$. There is a probability law $\mu$ on all nonnegative operators $\sigma_{DE}$ with $\operatorname{tr}_E\sigma_{DE}=\sigma_D$, chosen independently of $n$ and of the extension below. For every positive integer $n$ and every permutation-invariant nonnegative extension $\rho_{D^nE^n}$ of $\sigma_D^{\otimes n}$,
--
--   $$\rho_{D^nE^n}\le(n+1)^{d^2-1}\int\sigma_{DE}^{\otimes n}\,d\mu(\sigma_{DE}).$$
--
--   The order is Loewner order and all matrix coefficients of the integral are integrable. The marginal and its extensions need not have trace one. This is the fixed-marginal de Finetti reduction.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 12, Corollary 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Corollary 3.2 (PDF p.12): one law before all n and all extensions.
Coordinate integrability rules out the default value for a nonexistent integral. -/
theorem corollary3_2 {D E : Type*} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E] [Nonempty D] [Nonempty E]
    (sigma : Op D) (hsigma : sigma.PosSemidef) :
    letI := extensionMeasurable (E := E) sigma
    ∃ mu : Measure (Extensions (E := E) sigma), IsProbabilityMeasure mu ∧
      (∀ (n : ℕ) x y, Integrable (fun Z : Extensions (E := E) sigma =>
        groupedPower Z.val n x y) mu) ∧
      ∀ (n : ℕ), 0 < n → ∀ rho : Op ((Fin n → D) × (Fin n → E)),
        rho.PosSemidef → GroupInvariant rho → traceRight rho = matrixPower sigma n →
        OperatorLE rho (((((n+1 : ℕ) : ℝ) ^ (dimensionParameter D E ^ 2 - 1) : ℝ) : ℂ) •
          (fun x y => ∫ Z : Extensions (E := E) sigma, groupedPower Z.val n x y ∂mu)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
