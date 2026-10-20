-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P14_qubitComponent_not_lieSubsemigroup
-- name    : QAlgorithms.Papers.Independent.Dependency50.P14.qubitComponent_not_lieSubsemigroup
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:46:49.644087+00:00
-- url     : https://prove2.me/theorems/6cc98cb3-d187-48e2-a65f-5a7efe5188f8
-- title:
--   The invertible qubit channel component is not a Lie subsemigroup
-- statement:
--   Let $P_{\mathrm{cp}}^0$ be the identity component of the invertible CPTP maps on the real Hermitian $2\times2$ matrices, and let $\mathcal L$ denote the smooth one-sided curve tangent cone. Then
--
--   $$
--   P_{\mathrm{cp}}^0\text{ is not a Lie subsemigroup}.
--   $$
--
--   Here a Lie subsemigroup is a closed identity-containing multiplicative subset $S$ satisfying $S=\overline{\langle\exp(\mathcal L(S))\rangle_S}$, with closure relative to invertible maps. Thus the conclusion concerns failure of exponential generation up to closure, even though the component is a closed multiplicative semigroup.
--
--   This retains the source's explicitly rigorous qubit consequence separately from its unsupported extension to general dimension.
-- source:
--   Lie-Semigroup Structures for Reachability and Control of Open Quantum Systems, arXiv:0811.3906v4, PDF p. 8, Corollary III.2 rigorous qubit clause

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P14

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P14

open QAlgorithms.Papers.Independent.Information100.P59 (Operator dissipator)

/-- arXiv:0811.3906v4 PDF p.8, Corollary III.2: explicitly rigorous N=2 clause.
The component is still a closed multiplicative semigroup. -/
theorem qubitComponent_not_lieSubsemigroup :
    ¬ IsLieSubsemigroup (channelComponent 2) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P14

end
