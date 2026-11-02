-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_extensionCertificate
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.extensionCertificate
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:48:09.49139+00:00
-- url     : https://prove2.me/theorems/b07efb39-744d-40fd-978b-116301bc4631
-- title:
--   IV B: soundness of a candidate degrading-map extension certificate
-- statement:
--   Let $P\succeq0$ be an operator on finite nonempty systems $A\otimes B$, in a fixed product basis. Make exact copies $E_1=A$, $E_2=B$, and construct $|\psi\rangle=\operatorname{vec}\sqrt P$, with the physical $AB$ registers first. Let $N:E_1\to B'$ be any specified completely positive trace-preserving channel, where $B'$ is a copy of $B$, and put $E=N\circ\operatorname{Tr}_{E_2}$. Let $W=\operatorname{Tr}_B|\psi\rangle\langle\psi|$. If the tested antidegrading equality holds,
--
--   $$(\mathrm{id}_A\otimes E)(W)=P,$$
--
--   then $\operatorname{Tr}_{E_1E_2}|\psi\rangle\langle\psi|=P$, and the constructed operator
--
--   $$R=(\mathrm{id}_{AB}\otimes E)(|\psi\rangle\langle\psi|)$$
--
--   is positive and has both $AB$ and $AB'$ marginals equal to $P$. Hence $P$ is Bob-extendable. The complementary map is not assumed trace preserving. This is a soundness certificate for a candidate $N$, including $P=0$, and does not specify the particular experimental map or assert nonextendability when a candidate fails.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 9, IV B: soundness of a candidate degrading-map extension certificate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF pp.8–9, IV B steps 1–3: soundness for any candidate channel N satisfying
the tested antidegrading equality. This does not identify the experimental special N. -/
theorem extensionCertificate [Nonempty A] [Nonempty B]
    (P : Matrix (A × B) (A × B) ℂ) (hP : P.PosSemidef)
    (N : Superop A B) (hN : IsChannel N)
    (htest : idTensorSuperop (candidateDegrader N) (complementaryOperator P) = P) :
    traceRight (pureDensity (vectorPurification P)) = P ∧
    IsBobCopyExtension P (candidateExtension P N) ∧ BobExtendible P := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
