-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_measurementDiscord_continuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.measurementDiscord_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:31:29.308988+00:00
-- url     : https://prove2.me/theorems/aba22551-fb65-4fdd-9b44-99983d158a2b
-- title:
--   Global continuity bound for measurement-based quantum discord
-- statement:
--   Let $\rho,\sigma$ be density operators on nonzero finite-dimensional systems $A\otimes B$, with $D=\dim(A\otimes B)$ and $t=\|\rho-\sigma\|_1$. Let $D^{\leftarrow}$ be discord optimized over general local measurement operators on $B$, with arbitrary discrete outcome sets satisfying $\sum_kM_k^\dagger M_k=I_B$, and zero-probability conditional terms set to zero. Then
--
--   $$|D^{\leftarrow}(\rho)-D^{\leftarrow}(\sigma)|\le2t\log_2D+4h_2(t/2).$$
--
--   The entropy $h_2$ is in bits. This retains the stated general-measurement domain and the source constants.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 18, Theorem S17

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF pp.18–19, Theorem S17, S80: general measurements are retained despite
the proof's unjustified bound on the outcome-register dimension. -/
theorem measurementDiscord_continuity {A B : Type}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    |measurementDiscord rho - measurementDiscord sigma| ≤
      2 * traceNorm (rho - sigma) * Real.logb 2 (Fintype.card (A × B)) +
        4 * binEntropy2 (traceNorm (rho - sigma) / 2) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
