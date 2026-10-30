-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_cc_relativeEntropy_continuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.cc_relativeEntropy_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:28:16.929871+00:00
-- url     : https://prove2.me/theorems/cb8fea9e-70bc-443e-98a8-b7b622a1b556
-- title:
--   Global continuity bound for classical–classical relative entropy discord
-- statement:
--   Let $\rho,\sigma$ be density operators on nonzero finite-dimensional systems $A\otimes B$, put $D=\dim(A\otimes B)$ and $t=\|\rho-\sigma\|_1$, and let $h_2$ be binary entropy in bits with $0\log 0=0$. Classical–classical relative entropy discord, optimized over all local bases, is finite and satisfies
--
--   $$|D_{\rm cc}(\rho)-D_{\rm cc}(\sigma)|\le t\log_2 D+2h_2(t/2).$$
--
--   This global bound supplies asymptotic continuity without a small-distance premise.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 13, Theorem S10

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF pp.13–14, Theorem S10, S36: global full-trace-norm bound.
Inherited correction D2: printed c-c states use one paired k; changed to every
independent local product outcome, since paired outcomes fail normalization
on I4/4. No constant or hypothesis of S36 is changed; independently checked
in round 1. -/
theorem cc_relativeEntropy_continuity {A B : Type}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    normalizedResourceDistance classicalClassical rho ≠ ⊤ ∧ normalizedResourceDistance classicalClassical sigma ≠ ⊤ ∧
    |(normalizedResourceDistance classicalClassical rho).toReal -
      (normalizedResourceDistance classicalClassical sigma).toReal| ≤
      traceNorm (rho - sigma) * Real.logb 2 (Fintype.card (A × B)) +
        2 * binEntropy2 (traceNorm (rho - sigma) / 2) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
