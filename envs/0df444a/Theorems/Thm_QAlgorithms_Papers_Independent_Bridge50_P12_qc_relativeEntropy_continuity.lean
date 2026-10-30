-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_qc_relativeEntropy_continuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.qc_relativeEntropy_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:29:44.764288+00:00
-- url     : https://prove2.me/theorems/8cdd14ca-2dfe-4a35-bfc2-dd245ddb344f
-- title:
--   Global continuity bound for quantum–classical relative entropy discord
-- statement:
--   Let $\rho,\sigma$ be density operators on nonzero finite-dimensional systems $A\otimes B$. Set $D=\dim(A\otimes B)$ and $t=\|\rho-\sigma\|_1$. Relative entropy discord $D_{\rm qc}$, with the classical register on $B$ and its basis optimized, is finite and obeys
--
--   $$|D_{\rm qc}(\rho)-D_{\rm qc}(\sigma)|\le t\log_2D+2h_2(t/2).$$
--
--   Here $h_2$ is binary entropy in bits. This is the global continuity estimate for the specified orientation.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 15, Theorem S14

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF pp.15–16, Theorem S14, S54: global q-c bound, with the source orientation. -/
theorem qc_relativeEntropy_continuity {A B : Type}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    normalizedResourceDistance quantumClassical rho ≠ ⊤ ∧ normalizedResourceDistance quantumClassical sigma ≠ ⊤ ∧
    |(normalizedResourceDistance quantumClassical rho).toReal -
      (normalizedResourceDistance quantumClassical sigma).toReal| ≤
      traceNorm (rho - sigma) * Real.logb 2 (Fintype.card (A × B)) +
        2 * binEntropy2 (traceNorm (rho - sigma) / 2) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
