-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_amplitude_damping_discrimination
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.amplitude_damping_discrimination
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:47:03.367665+00:00
-- url     : https://prove2.me/theorems/b42ca42d-c874-438d-a64d-ca86bfbbbf08
-- title:
--   §II.J, Eqs.(34),(37): adaptive lower and block bounds
-- statement:
--   Let $p,q\in[0,1]$, $n\ge1$, and integer $M\ge2$. Write $F=[1+\sqrt{(1-p)(1-q)}+\sqrt{pq}]/2$, $\Delta_M(p)=\xi_M[(1-p)/2+\sqrt{1-p}]$, and $\overline\Delta_M=[\Delta_M(p)+\Delta_M(q)]/2$. The equally likely amplitude-damping channels satisfy
--
--   $$p_n\ge\frac{1-n\overline\Delta_M-\sqrt{1-F^{2nM}}}{2}.$$
--
--   For independent Bell probes with one joint optimal measurement, let $p_n^{\rm block}=[1-D(\rho_{\mathcal E_p}^{\otimes n},\rho_{\mathcal E_q}^{\otimes n})]/2$. Then
--
--   $$p_n\le p_n^{\rm block},\qquad\frac{1-\sqrt{1-F^{2n}}}{2}\le p_n^{\rm block}\le\frac{F^n}{2}.$$
--
--   The block lower bound constrains the block strategy alone; the exact adaptive optimum remains unspecified.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 6, §II.J, Eqs.(34),(37): adaptive lower and block bounds

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

/-- PDF pp.6--7, (34),(37): adaptive lower bound and distinct nonadaptive
block sandwich. No claim of optimality of the block strategy is made. -/
theorem amplitude_damping_discrimination (n M : ℕ) (hn : 1 ≤ n) (hM : 2 ≤ M)
    (p q : ℝ) (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    let E0 := amplitudeDampingChannel p
    let E1 := amplitudeDampingChannel q
    let F := dampingFidelity p q
    (1-n*((dampingSimulationError M p+dampingSimulationError M q)/2) -
      Real.sqrt (1-F^(2*n*M)))/2 ≤ symmetricAdaptiveError n E0 E1 ∧
    symmetricAdaptiveError n E0 E1 ≤ bellProbeBlockError n E0 E1 ∧
    (1-Real.sqrt (1-F^(2*n)))/2 ≤ bellProbeBlockError n E0 E1 ∧
    bellProbeBlockError n E0 E1 ≤ F^n/2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
