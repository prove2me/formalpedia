-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_jointConvexityRecovery
-- name    : QAlgorithms.Papers.Independent.Dependency50.P21.jointConvexityRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:15:04.367861+00:00
-- url     : https://prove2.me/theorems/f0951e9a-5bbb-4a17-a366-af219324cbcc
-- title:
--   Joint convexity gap bounds cq recovery fidelity
-- statement:
--   Let X be finite, let ν be a probability vector, and let each σˣ be a positive operator on a finite-dimensional complex system A. For every x let ρˣ be a density operator supported in σˣ. Put σXA=∑xν(x)|x⟩⟨x|⊗σˣ, ρXA=∑xν(x)|x⟩⟨x|⊗ρˣ, σA=∑xν(x)σˣ and ρA=∑xν(x)ρˣ. Define R:A→XA by (21) from σXA and trX. Then
--
--   $$\sum_{x\in X}\nu(x)D(\rho^x\|\sigma^x)-D(\rho_A\|\sigma_A)\ge -2\log F\bigl(\rho_{XA},\mathcal R(\rho_A)\bigr).$$
--
--   All relative entropies in this gap are finite, although σˣ need not be normalized and the values may be negative. The bound retains the full joint convexity gap.
--
--   **Source correction.** This is the well-typed fidelity bound (109)-(111) in the proof. The malformed block expression (108)/(112), including its undefined S and missing block normalization, is not asserted. The average is t/2 as in (21).
-- source:
--   Universal recovery maps and approximate sufficiency of quantum relative entropy, arXiv:1509.07127v3, PDF p. 17, Corollary 4.3; proof (109)-(111) on p.18

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P21

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the named interfaces from the pinned accepted paper library.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- Corollary 4.3, PDF pp.17-18: the well-typed conclusion is Eq.(111), with the
entire joint-convexity gap of Eq.(110). SOURCE CORRECTION: Eq.(108)'s undefined S and
mismatched state/operator types are replaced by the cq fidelity of Eqs.(109)-(111).
Also use Eq.(21)'s t/2 average. The references sigma_x are not normalized. -/
theorem jointConvexityRecovery {X I : Type*} [Fintype X] [Fintype I]
    [DecidableEq X] [DecidableEq I] (nu : X → ℝ) (sigma states : X → Mat I)
    (hnu : ∀ x, 0 ≤ nu x) (hsum : (∑ x, nu x) = 1)
    (hsigma : ∀ x, (sigma x).PosSemidef) (hstates : ∀ x, IsDensityMatrix (states x))
    (hsupport : ∀ x, IsSupported (states x) (sigma x)) :
    relativeEntropy (∑ x, (nu x : ℂ) • states x) (∑ x, (nu x : ℂ) • sigma x) +
      fidelityPenalty (rootFidelity (cqOperator nu states)
        (recovery (cqOperator nu sigma) (traceLeft (α := X) (β := I))
          (∑ x, (nu x : ℂ) • states x))) ≤
      ∑ x, (nu x : EReal) * relativeEntropy (states x) (sigma x) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P21

end
