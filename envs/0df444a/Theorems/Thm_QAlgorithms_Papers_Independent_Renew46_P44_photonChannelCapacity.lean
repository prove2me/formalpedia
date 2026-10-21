-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_photonChannelCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.photonChannelCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:38:58.921008+00:00
-- url     : https://prove2.me/theorems/9362d1ab-89f6-4eb0-b187-e6343592d1a8
-- title:
--   §V.1, (92)–(95): photon-channel equivalence and optimal prior
-- statement:
--   For $N,E\ge0$, let $S_m=P^m\tau_N(P^\dagger)^m$ be the diagonal photon alphabet on the full number basis, with $P|j\rangle=|j+1\rangle$ and letter cost $m$. Its operational capacity under the per-word mean-number budget equals that of the displaced thermal channel:
--
--   $$C_{\rm photon}=C_{\rm Gaussian}=g(N+E)-g(N).$$
--
--   For $N+E>0$, the optimal law is
--
--   $$\pi_m=\frac N{N+E}\mathbf1_{m=0}+\frac E{N+E}\frac{(N+E)^m}{(N+E+1)^{m+1}}.$$
--
--   At $N=E=0$ use Dirac at zero. The displayed weights are nonnegative, sum to one, have mean $E$, and their output barycenter is $\tau_{N+E}$. The unilateral energy shift is an isometry, not a unitary. This establishes the source's asymptotic capacity equivalence.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 25, §V.1, (92)–(95): photon-channel equivalence and optimal prior

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.25-26, (92)-(95): photon/Gaussian capacity equivalence and the
explicit optimal photon distribution; the mean constraint is input energy E. -/
theorem photonChannelCapacity (N E : ℝ) (hN : 0 ≤ N) (hE : 0 ≤ E) :
    (∀ m, TC.IsDensity (photonOutput N m)) ∧
    (∀ m, 0 ≤ photonPrior N E m) ∧
    HasSum (photonPrior N E) 1 ∧
    HasSum (fun m : ℕ => (m : ℝ) * photonPrior N E m) E ∧
    (∀ i j, (∑' m, (photonPrior N E m : ℂ) * photonOutput N m i j) =
      F.thermalMatrix (2 * (N + E) + 1) i j) ∧
    (∑' m, ENNReal.ofReal (photonPrior N E m) *
      QE.extendedRelativeEntropyNats (photonOutput N m)
        (F.thermalMatrix (2 * (N + E) + 1))) = ENNReal.ofReal (g (N + E) - g N) ∧
    averageErrorCqCapacity (photonOutput N) (fun m => (m : ℝ)) E =
      averageErrorCqCapacity (gaussianOutput N) Complex.normSq E ∧
    averageErrorCqCapacity (photonOutput N) (fun m => (m : ℝ)) E =
      ENNReal.ofReal (g (N + E) - g N) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
