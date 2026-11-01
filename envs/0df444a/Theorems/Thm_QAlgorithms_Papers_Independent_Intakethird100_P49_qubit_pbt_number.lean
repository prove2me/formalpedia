-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_qubit_pbt_number
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.qubit_pbt_number
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:37:27.764492+00:00
-- url     : https://prove2.me/theorems/cdeed2f7-965e-43c2-9e98-3c7285329cfc
-- title:
--   Eq.(11), Supplement I: exact qubit PBT number
-- statement:
--   For standard qubit PBT with integer $M\ge2$, put $s_k=(M-1)/2-k$ for $0\le k\le\lfloor(M-1)/2\rfloor$. The actual depolarizing probability is
--
--   $$\xi_M=\frac{M+2}{3\,2^{M-1}}+\frac13\sum_{k=0}^{\lfloor(M-1)/2\rfloor}\frac{s_k(s_k+1)}{2^{M-4}}\binom Mk\frac{M+2-\sqrt{(M+2)^2-(2s_k+1)^2}}{(M+2)^2-(2s_k+1)^2}.$$
--
--   The powers are real powers, so negative exponents at $M=2,3$ are retained. In particular $\xi_2=(6-\sqrt3)/6$ and $\xi_3=1/2$. The formula makes the qubit simulation error explicit without assuming an optimized or probabilistic teleportation resource.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 3, Eq.(11), Supplement I: exact qubit PBT number

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

/-- PDF p.3, (11), Supplement I and p.9, (58): exact qubit PBT number.
The two smallest admissible port counts also pin its indexing convention. -/
theorem qubit_pbt_number :
    (∀ M : ℕ, 2 ≤ M → pbtNumber 2 M = qubitNumberFormula M) ∧
    pbtNumber 2 2 = (6-Real.sqrt 3)/6 ∧ pbtNumber 2 3 = 1/2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
