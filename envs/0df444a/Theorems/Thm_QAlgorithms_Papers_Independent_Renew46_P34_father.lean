-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_father
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.father
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:07:25.393606+00:00
-- url     : https://prove2.me/theorems/c54942ec-054f-427b-98dd-fa5e2300535f
-- title:
--   Father: entanglement-assisted quantum communication
-- statement:
--   Let $\mathcal N:A^{\prime}\to B$ be a finite-dimensional CPTP channel with Stinespring isometry $U:A^{\prime}\to B\otimes E$. Fix a unit vector $|\phi\rangle^{AA^{\prime}}$ and construct $|\psi\rangle^{ABE}=(1_A\otimes U)|\phi\rangle$. Every register is nonzero. Entropies and mutual informations are in bits and refer to this constructed state; $I_c(A\rangle B)=H(B)-H(AB)$.
--
--   The channel has the fixed-input achievable resource conversion
--
--   $$\tfrac12 I(A;E)[qq]+\{q\to q\}\ge\tfrac12 I(A;B)[q\to q].$$
--
--   Here $\ge$ is operational achievability: for every error $\varepsilon>0$ and rate slack $\delta>0$, protocols exist at every sufficiently large block length $n$. They use $n$ independent copies or uses of the noisy resource. Each displayed consumed rate has an upper slack $\delta$ and each produced rate has a lower slack $\delta$; absent input resources are exactly absent. A negative coefficient is moved to the other side as a positive input resource. Local operations and local ancillary registers are free. Communication codes are chosen before the unknown input, and error is bounded in trace distance uniformly over inputs and all finite reference extensions. This states the displayed achievable resource pair without optimization or a capacity converse.
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 2, Father resource inequality (♂)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1–2, father RI: fixed pure input and its actual Stinespring output;
quantum-channel simulation is uniform over unknown inputs and reference extensions. -/
theorem father {A X B E : Type}
    [Fintype A] [Fintype X] [Fintype B] [Fintype E]
    [Nonempty A] [Nonempty X] [Nonempty B] [Nonempty E]
    (D : ChannelData X B E) (phi : EuclideanSpace ℂ (A × X)) (hphi : IsState phi) :
    DynamicRI D.channel 0 (informationAB (channelPsi D phi) / 2)
      (-informationAE (channelPsi D phi) / 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
