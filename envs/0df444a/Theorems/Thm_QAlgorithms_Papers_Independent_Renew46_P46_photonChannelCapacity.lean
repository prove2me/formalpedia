-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_photonChannelCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.photonChannelCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:54:08.080355+00:00
-- url     : https://prove2.me/theorems/72a3c14e-e843-44bb-8c1a-247afc12ffd5
-- title:
--   §III: photon-channel optimizer and capacity equivalence
-- statement:
--   For finite $N,E\ge0$, let $S_m=P^mS_0(P^*)^m$ on full Fock space, where $P|j\rangle=|j+1\rangle$ and $S_0$ is thermal of mean $N$. These are density operators, diagonal with entry $(N/(N+1))^{j-m}/(N+1)$ for $j\ge m$ and zero otherwise, with entropy $h(N)$ and photon mean $N+m$. Define the input weights, when $N+E>0$, by
--
--   $$\pi_m=\frac{N}{N+E}\mathbf1_{m=0}+\frac{E}{N+E}\frac{(N+E)^m}{(N+E+1)^{m+1}},$$
--
--   and set $\pi=\delta_0$ when $N=E=0$. This is an admissible probability law with mean input cost $E$, its barycenter is thermal of mean $N+E$, and it maximizes the entropy difference under $\sum_m m\pi_m\le E$. Therefore
--
--   $$C_{\rm photon}=C_{\rm Gaussian}=\Delta H(\pi)=h(N+E)-h(N).$$
--
--   Here $h(t)=(t+1)\log(t+1)-t\log t$ in nats. The photon optimizer is credited to [14]; its use here establishes capacity equivalence.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 10, §III: photon-channel optimizer and capacity equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section III, PDF pp.9-10, (29)-(32), optimizer credited to [14]. The actual
shifted-thermal signals and actual optimal photon law have entropy h(N), means
N+m and E, thermal barycenter N+E, and capacity equal to the Gaussian cq channel. -/
theorem photonChannelCapacity (N E : ℝ) (hN : 0 ≤ N) (hE : 0 ≤ E) :
    ∃ (hP : ∀ m, constrainedCqDensity (photonSignal N m)) (hS : ∀ alpha, constrainedCqDensity (gaussianSignal N alpha)),
      (∀ m i j, constrainedCqCoefficient (photonSignal N m) i j =
        if i = j ∧ m ≤ i then (((N / (N + 1)) ^ (i - m) / (N + 1) : ℝ) : ℂ) else 0) ∧
      (∀ m, constrainedCqEntropy (photonSignal N m) = ENNReal.ofReal (h N) ∧
        constrainedCqPhotonMean (photonSignal N m) = ENNReal.ofReal (N + (m : ℝ))) ∧
      MeasureAdmissible (fun m : ℕ => (m : ℝ)) E (photonPrior N E) ∧
      (∫ m : ℕ, (m : ℝ) ∂photonPrior N E) = E ∧
      constrainedCqAverage (photonSignal N) (photonPrior N E) = constrainedCqThermal (N + E) ∧
      constrainedCqChi (photonSignal N) (photonPrior N E) = ENNReal.ofReal (h (N + E) - h N) ∧
      (∀ pi : Measure ℕ, MeasureAdmissible (fun m : ℕ => (m : ℝ)) E pi →
        constrainedCqChi (photonSignal N) pi ≤ constrainedCqChi (photonSignal N) (photonPrior N E)) ∧
      constrainedCqCapacity (stateFamily (photonSignal N) hP) (fun m : ℕ => (m : ℝ)) E =
        ENNReal.ofReal (h (N + E) - h N) ∧
      constrainedCqCapacity (stateFamily (photonSignal N) hP) (fun m : ℕ => (m : ℝ)) E =
        constrainedCqCapacity (stateFamily (gaussianSignal N) hS) energyCost E := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
