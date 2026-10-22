-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P16_transposeDepolarizing_capacityEntropy
-- name    : QAlgorithms.Papers.Independent.Gap20.P16.transposeDepolarizing_capacityEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:36:44.971686+00:00
-- url     : https://prove2.me/theorems/77546c82-825a-46d2-b959-06240f2228b8
-- title:
--   Transpose-depolarizing channel satisfies the capacity–entropy identity
-- statement:
--   Let $d\ge2$. In a fixed orthonormal basis define the channel on all complex $d\times d$ matrices by $\Phi(X)=(\operatorname{Tr}(X)I-X^{\mathsf T})/(d-1)$. This map is completely positive and trace preserving. On states this is the formula $(I-\rho^{\mathsf T})/(d-1)$. Then
--
--   $$
--   \bar C^{(1)}(\Phi)=\log_2d-\min_{\rho}H(\Phi(\rho)).
--   $$
--
--   Here $\rho$ ranges over all density matrices, $H$ is entropy in bits, and $\bar C^{(1)}$ maximizes the output Holevo quantity over all finite normalized state ensembles. The minimum and a finite-ensemble maximum are attained. This gives a concrete example of the capacity–entropy identity beyond the qubit-only setting.
-- source:
--   Remarks on the classical capacity of quantum channel, arXiv:quant-ph/0212025v1, PDF p. 2, §1, (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P16

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF p.2, (5): the transpose-depolarizing channel satisfies (2).
The accepted map is (Tr(X) I - transpose(X))/(d-1), so on trace-one states
it is exactly the printed formula. The denominator requires d >= 2;
the earlier accepted definition's use at d >= 3 is not imposed here. -/
theorem transposeDepolarizing_capacityEntropy {d : ℕ} (hd : 2 ≤ d) :
    IsChannel (QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d) ∧
    CapacityEntropyIdentity
      (QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo d) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P16

end
