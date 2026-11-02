-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_inverse_emulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.inverse_emulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:57:41.878197+00:00
-- url     : https://prove2.me/theorems/c947e533-1c5b-4cef-aad2-1d2ca82bedf9
-- title:
--   §III remarks: emulating the inverse with the same samples
-- statement:
--   Let $K\ge2$ normalized pure input samples generate the full algebra on their span, and let their output records be the exact images under an unknown unitary $U$. The output samples also generate the full algebra on their span $H_{\rm out}$. Running the same emulator with input and output samples exchanged gives, for every $\epsilon>0$, a threshold $N$ such that all $T\ge N$ and all density operators supported on $H_{\rm out}$ satisfy
--
--   $$\tfrac12\|\mathcal E_{\rm reverse,T}(\rho)-U^\dagger\rho U\|_1\le\epsilon.$$
--
--   The threshold is uniform over the new input. The construction uses the supplied records in reverse roles; it does not query an inverse-unitary oracle.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 4, §III remarks: emulating the inverse with the same samples

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.4: swapping the supplied records implements U-dagger uniformly on H_out.
The circuit accesses samples, not a callable U-dagger. -/
theorem inverse_emulation (phi : K → EuclideanSpace ℂ I) (a : K)
    (hK : 2 ≤ Fintype.card K) (hphi : ∀ k, IsState (phi k))
    (hgen : Generates (pureSamples phi)) (U : Matrix.unitaryGroup I ℂ) :
    let out := fun k => act (U : Matrix I I ℂ) (phi k)
    Generates (pureSamples out) ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ T ≥ N,
      ∀ rho : Matrix I I ℂ, IsDensityMatrix rho → InSampleSupport (pureSamples out) rho →
      traceDistance (emulate out a (U : Matrix I I ℂ)ᴴ T rho) (densityConjugation (U : Matrix I I ℂ)ᴴ rho) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
