-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P14_qubitComponent_not_local
-- name    : QAlgorithms.Papers.Independent.Dependency50.P14.qubitComponent_not_local
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:47:36.068561+00:00
-- url     : https://prove2.me/theorems/d38f507c-0dd2-4fa2-bc95-96a0fea4b542
-- title:
--   Qubit channel wedges fail local divisibility, exponentiality, and BCH compatibility
-- statement:
--   Let $P_{\mathrm{cp}}^0$ be the identity component of the invertible CPTP maps on the real Hermitian $2\times2$ matrices, and let $W=\mathcal L(P_{\mathrm{cp}}^0)$ be its one-sided smooth-curve tangent cone. Then
--
--   $$
--   P_{\mathrm{cp}}^0\text{ is not locally divisible},\qquad
--   P_{\mathrm{cp}}^0\text{ is not locally exponential},\qquad
--   W\text{ is not a Lie semialgebra}.
--   $$
--
--   Local divisibility requires a relative identity-neighborhood basis consisting of subsets in which every element has roots of every positive integer order. Local exponentiality requires such a basis of exponential subsets, where each element lies on a short exponential arc entirely contained in the subset. A Lie semialgebra is a closed convex real cone stable under the local Baker–Campbell–Hausdorff product on some zero-neighborhood.
--
--   These are the three conclusions of the source in its explicitly proved qubit scope. The local properties quantify over an entire relative neighborhood basis.
-- source:
--   Lie-Semigroup Structures for Reachability and Control of Open Quantum Systems, arXiv:0811.3906v4, PDF p. 9, Corollary III.3 rigorous qubit clause

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P14

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P14

open QAlgorithms.Papers.Independent.Information100.P59 (Operator dissipator)

/-- arXiv:0811.3906v4 PDF p.9, Corollary III.3: all three negative conclusions
in the explicitly rigorous N=2 case. -/
theorem qubitComponent_not_local :
    ¬ IsLocallyDivisible (channelComponent 2) ∧
    ¬ IsLocallyExponential (channelComponent 2) ∧
    ¬ IsLieSemialgebra (tangent (channelComponent 2)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P14

end
