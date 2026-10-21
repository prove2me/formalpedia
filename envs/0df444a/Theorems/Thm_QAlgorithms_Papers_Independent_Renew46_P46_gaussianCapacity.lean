-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_gaussianCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.gaussianCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:53:14.186297+00:00
-- url     : https://prove2.me/theorems/29959098-2cf5-4744-8b0c-69dbe859b295
-- title:
--   §III: Gaussian signal capacity and optimizing law
-- statement:
--   Let $N,E\ge0$ be finite. For the full-Fock displaced-thermal channel $\alpha\mapsto S_\alpha$ of noise mean $N$, use the mean input constraint $\int|\alpha|^2\,\pi(d\alpha)\le E$ and the per-word operational cost convention. Let $G_E$ be the circular Gaussian input law of variance $E$, interpreted as $\delta_0$ when $E=0$. Put $h(t)=(t+1)\log(t+1)-t\log t$. The signal family consists of density operators, $G_E$ is admissible with mean cost exactly $E$, and its actual barycenter is the thermal state of photon mean $N+E$. Moreover the uniform average-state entropy bound holds and
--
--   $$C=\Delta H(G_E)=h(N+E)-h(N),\qquad \Delta H(\pi)\le\Delta H(G_E)\quad(\pi\text{ admissible}).$$
--
--   Thus the specified Gaussian law attains capacity in nats, including both zero endpoints.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 9, §III: Gaussian signal capacity and optimizing law

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section III, PDF p.9, (24)-(28): exact Gaussian cq capacity and an actual
attaining prior. The entropy-difference form includes both zero endpoints.
There is no transmissivity or arbitrary-quantum-input channel in this result. -/
theorem gaussianCapacity (N E : ℝ) (hN : 0 ≤ N) (hE : 0 ≤ E) :
    ∃ hS : ∀ alpha, constrainedCqDensity (gaussianSignal N alpha),
      MeasureAdmissible energyCost E (gaussian E) ∧
      (∫ alpha, energyCost alpha ∂gaussian E) = E ∧
      constrainedCqAverage (gaussianSignal N) (gaussian E) = constrainedCqThermal (N + E) ∧
      MeasureEntropyBound (gaussianSignal N) energyCost E ∧
      constrainedCqChi (gaussianSignal N) (gaussian E) = ENNReal.ofReal (h (N + E) - h N) ∧
      constrainedCqCapacity (stateFamily (gaussianSignal N) hS) energyCost E =
        ENNReal.ofReal (h (N + E) - h N) ∧
      (∀ pi : Measure ℂ, MeasureAdmissible energyCost E pi →
        constrainedCqChi (gaussianSignal N) pi ≤ constrainedCqChi (gaussianSignal N) (gaussian E)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
