-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_amplitude_damping_simulation_error
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.amplitude_damping_simulation_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:45:54.348557+00:00
-- url     : https://prove2.me/theorems/7a426fc6-a655-4f57-a627-54ac8e060069
-- title:
--   Eq.(36), Methods IV.C: exact amplitude-damping simulation error
-- statement:
--   Let $p\in[0,1]$, integer $M\ge2$, and let $\xi_M$ be the standard qubit PBT number. For the actual channel $\mathcal E_p$ with excited state $|1\rangle$ decaying to $|0\rangle$, set $\mathcal E_p^M=\mathcal E_p\circ\Gamma_{2,M}$. Its unhalved diamond error is
--
--   $$\|\mathcal E_p-\mathcal E_p^M\|_\diamond=\xi_M\left(\frac{1-p}{2}+\sqrt{1-p}\right).$$
--
--   This makes the channel-specific bound computable. The supporting Choi calculation corrects the second diagonal in printed Eq. (59) from $(1-p)\xi_M$ to $(1-p)\xi_M/4$, as required by the Kraus action and unit trace; independent moderation of this correction is pending.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 7, Eq.(36), Methods IV.C: exact amplitude-damping simulation error

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

/-- PDF p.7, (36), Methods p.9: actual diamond simulation error.
Source correction in supporting (59): printed second diagonal (1-p)*xi
must be (1-p)*xi/4, as forced by applying (33) to (57) and unit trace.
This correction requires independent moderation. -/
theorem amplitude_damping_simulation_error (M : ℕ) (hM : 2 ≤ M)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    diamond (fun X => amplitudeDampingChannel p X -
      simulated (amplitudeDampingChannel p) M X) = dampingSimulationError M p := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
