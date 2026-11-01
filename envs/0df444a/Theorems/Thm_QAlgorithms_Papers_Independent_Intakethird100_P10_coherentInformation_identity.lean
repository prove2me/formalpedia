-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_coherentInformation_identity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.coherentInformation_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:39:19.01725+00:00
-- url     : https://prove2.me/theorems/52b7f090-3a14-4592-a435-7577bd59ae85
-- title:
--   Symmetric coherent information as a cq information difference
-- statement:
--   Let $U:\mathbb C^2\to B\otimes E$ be an isometry with finite nonempty output registers, and choose any orthonormal qubit input basis. Let $W$ and $W^*$ be the cq channels induced in that basis by tracing out $E$ and $B$, respectively. Let $\omega^{AB}$ be obtained by sending the second half of the normalized Bell state through this same isometry and discarding $E$. Then
--
--   $$
--   I_{\mathrm c}^{\mathrm{sym}}(U):=H(\omega^B)-H(\omega^{AB})=I(W)-I(W^*).
--   $$
--
--   All entropies are in bits. The register $A$ here is the retained Bell reference. Neither degradability nor commuting environment outputs are required, and no optimization over input density matrices occurs.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 6, §IV, unnumbered symmetric coherent information identity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF pp.6–7, unnumbered identity: no degradation or commuting-environment assumption.
The normalized Bell input and the two cq channels use one orthonormal input basis. -/
theorem coherentInformation_identity {B E : Type*}
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (U : Matrix (B × E) Bool ℂ) (hU : Uᴴ * U = 1)
    (basis : Matrix.unitaryGroup Bool ℂ) :
    symmetricCoherentInformation U basis =
      symmetricInformation (dilationBob U basis) - symmetricInformation (dilationEve U basis) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
