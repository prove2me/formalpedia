-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_amplitude_damping_choi_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.amplitude_damping_choi_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:45:04.857791+00:00
-- url     : https://prove2.me/theorems/6029e42c-9715-4c95-b6b7-bb5e4efb2a27
-- title:
--   §II.J, Eq.(35): amplitude-damping Choi fidelity
-- statement:
--   Let $p,q\in[0,1]$ and let $\mathcal E_p$ be the qubit amplitude-damping channel with $K_0=|0\rangle\langle0|+\sqrt{1-p}|1\rangle\langle1|$ and $K_1=\sqrt p|0\rangle\langle1|$. For normalized reference-first Choi states,
--
--   $$F(\rho_{\mathcal E_p},\rho_{\mathcal E_q})=\frac{1+\sqrt{(1-p)(1-q)}+\sqrt{pq}}2.$$
--
--   Here $F$ is root fidelity. This gives the explicit overlap entering both the adaptive lower bound and the Bell-probe block bounds.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 7, §II.J, Eq.(35): amplitude-damping Choi fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P49

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond AdaptiveTest adaptiveInput adaptiveAccept)

open QAlgorithms.Papers.Independent.Bridge50.P25
  (LOCCOn normalizedChannelChoi TwoWayGenerationCode TwoWayChannelProtocol
   generationCodeError twoWayGenerationCapacity sendChannelRegister StateFunctional
   IsDimensionChangingLOCCMonotone privateStateInPartyOrder)

open QAlgorithms.Papers.Independent.Support50.P07 (amplitudeDampingChannel)

/-- PDF pp.6--7, (32)--(35): Choi ROOT fidelity for the frozen actual
amplitude-damping channel, excited |1> decaying to |0>. -/
theorem amplitude_damping_choi_fidelity (p q : ℝ)
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    rootFidelity (normalizedChannelChoi (amplitudeDampingChannel p))
      (normalizedChannelChoi (amplitudeDampingChannel q)) = dampingFidelity p q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
