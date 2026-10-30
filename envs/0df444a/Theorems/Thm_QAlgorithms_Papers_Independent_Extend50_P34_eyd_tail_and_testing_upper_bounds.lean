-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_eyd_tail_and_testing_upper_bounds
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.eyd_tail_and_testing_upper_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:54:10.99856+00:00
-- url     : https://prove2.me/theorems/d7d9fc8e-f480-4e3d-8c18-1be5d586c7cb
-- title:
--   Corollary 3.2
-- statement:
--   Let $\rho$ be a $d$-dimensional density matrix with decreasing eigenvalues $\eta$, where $d\ge2$. For EYD with $n\ge1$ and $0<\epsilon<1$,
--
--   $$\Pr[d_{\rm TV}(\bar\lambda,\eta)>\epsilon]\le(n+1)^{d(d+1)/2}e^{-2n\epsilon^2}.$$
--
--   Consequently, for $0<\delta\le1/3$, $O(d^2\epsilon^{-2}\log(d/\epsilon)\log(1/\delta))$ copies suffice for an $\epsilon$-accurate estimate with probability at least $1-\delta$, uniformly in $\rho$. Every closed unitarily invariant property is therefore testable with $O(d^2\epsilon^{-2}\log(d/\epsilon))$ copies and success probability $2/3$. These bounds give a general spectrum-testing upper bound.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 29, Corollary 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Corollary 3.2, arXiv:1501.05028v1, PDF p.29. Preserve the finite-n tail and both consequences. delta≤1/3 prevents a vanishing log(1/delta) rounding bound; universal constants precede state and property. -/
theorem eyd_tail_and_testing_upper_bounds
    : (∀ d n : ℕ, 2 ≤ d → 0 < n →
        ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
        ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
          (∑ lambda : Schur.Partition d n, sw rho lambda *
            (if epsilon < eydError n (decreasingSpectrum rho) lambda.val then 1 else 0)) ≤
          (n+1 : ℝ)^(d*(d+1)/2) * Real.exp (-2*n*epsilon^2)) ∧
      (∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
        ∀ epsilon delta : ℝ, 0 < epsilon → epsilon < 1 → 0 < delta → delta ≤ 1/3 →
          ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤
            A*d^2/epsilon^2 * Real.log (d/epsilon) * Real.log (1/delta) ∧
            ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
              (∑ lambda : Schur.Partition d n, sw rho lambda *
                (if epsilon < eydError n (decreasingSpectrum rho) lambda.val then 1 else 0)) ≤ delta) ∧
      (∃ A : ℝ, 0 < A ∧ ∀ d : ℕ, 2 ≤ d →
        ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
          ∀ P : Set (Fin d → ℝ), IsSpectralProperty P →
            ∃ n : ℕ, (n : ℝ) ≤ A*d^2/epsilon^2 * Real.log (d/epsilon) ∧
              QuantumTestable d n P epsilon) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
