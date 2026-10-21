-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_noisy_teleportation
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.noisy_teleportation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:11:01.432226+00:00
-- url     : https://prove2.me/theorems/b4c26c07-8e4f-4373-9048-a5f89fef41d6
-- title:
--   Noisy teleportation
-- statement:
--   Let $|\psi\rangle^{ABE}$ be a unit vector on finite nonzero registers, and let $\rho^{AB}=\operatorname{Tr}_E|\psi\rangle\langle\psi|$. All entropies are in bits and are evaluated on this same state. Write $I(A;B)=H(A)+H(B)-H(AB)$, $I(A;E)=H(A)+H(E)-H(AE)$ and $I_c(A\rangle B)=H(B)-H(AB)$.
--
--   The achievable conversion is
--
--   $$I(A;B)[c\to c]+\{qq\}\ge I_c(A\rangle B)[q\to q].$$
--
--   Here $\ge$ is operational achievability: for every error $\varepsilon>0$ and rate slack $\delta>0$, protocols exist at every sufficiently large block length $n$. They use $n$ independent copies or uses of the noisy resource. Each displayed consumed rate has an upper slack $\delta$ and each produced rate has a lower slack $\delta$; absent input resources are exactly absent. A negative coefficient is moved to the other side as a positive input resource. Local operations and local ancillary registers are free. Communication codes are chosen before the unknown input, and error is bounded in trace distance uniformly over inputs and all finite reference extensions. This states the displayed achievable resource pair without optimization or a capacity converse.
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 2, (1): noisy teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, (1): noisy teleportation, including negative coherent information as input. -/
theorem noisy_teleportation {A B E : Type}
    [Fintype A] [Fintype B] [Fintype E] [Nonempty A] [Nonempty B] [Nonempty E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) (hpsi : IsState psi) :
    StaticRI (sourceAB psi) (-informationAB psi) ((vnEntropy (traceLeft (sourceAB psi)) - vnEntropy (sourceAB psi))) 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
