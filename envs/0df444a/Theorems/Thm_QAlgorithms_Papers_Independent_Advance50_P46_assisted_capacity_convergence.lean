-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_assisted_capacity_convergence
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.assisted_capacity_convergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:20:31.842315+00:00
-- url     : https://prove2.me/theorems/66d8e027-d937-4a21-a8b2-cc30c7f617be
-- title:
--   Corollary C.2 (entanglement-assisted capacity)
-- statement:
--   Let the positive input Hamiltonian $H_A$ satisfy the Gibbs hypothesis and have ordered spectral-pair exponent $\eta$. Let $E>\inf\sigma(H_A)$ and $0<\varepsilon<1$, and suppose CPTP channels satisfy $\tfrac12\|\Phi-\Psi\|_\diamond^{H_A,E}\le\varepsilon$. The entanglement-assisted capacity is the supremum of the actual purification-based channel mutual information over input states of energy at most $E$. For $0<t\le1/(2\varepsilon)$ and $r=(1+t/2)/(1-\varepsilon t)$,
--
--   $$|C_{\rm ea}(\Phi,H_A,E)-C_{\rm ea}(\Psi,H_A,E)|\le2\varepsilon(2t+r)F_{H_A}\!\left(\frac E{\varepsilon t}\right)+2g(\varepsilon r)+4h(\varepsilon t).$$
--
--   Both capacities are finite. No output energy assumption is made. Here $g(x)=(x+1)\log(x+1)-x\log x$ and $h$ is binary entropy in nats. The one input-Hamiltonian remainder gives $F_{H_A}(x)=\eta\log x(1+R_{H_A}(x))$ at high arguments, with $R_{H_A}(x)\to0$.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 47, Corollary C.2 (entanglement-assisted capacity)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Corollary C.2 (EAC), PDF pp.47--48. No output energy condition; the Gibbs
Hamiltonian belongs to the input. E>ground resolves the printed H/HA notation. -/
theorem assisted_capacity_convergence {I J : Type} [Countable I] [Infinite I]
    [Countable J] [Infinite J] (H : Spectral.Hamiltonian I)
    (hpos : ∀ i, 0 ≤ H.energy i) (hG : H.gibbs) (xi : ℝ) (hxi : HasPairRatio H xi)
    (Phi Psi : Spectral.Channel I J) (E epsilon : ℝ) (hE : semiboundedGroundEnergy H < E)
    (heps : 0 < epsilon) (heps1 : epsilon < 1)
    (hdist : spectralEnergyMagnitude H E (fun X => Phi.val X - Psi.val X) ≤
      ENNReal.ofReal (2 * epsilon)) :
    ThermalAsymptotic H xi ∧ constrainedPurificationCapacity Phi H E < ⊤ ∧ constrainedPurificationCapacity Psi H E < ⊤ ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 / (2 * epsilon) →
      |(constrainedPurificationCapacity Phi H E).toReal - (constrainedPurificationCapacity Psi H E).toReal| ≤
        assistedModulus H E epsilon t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
