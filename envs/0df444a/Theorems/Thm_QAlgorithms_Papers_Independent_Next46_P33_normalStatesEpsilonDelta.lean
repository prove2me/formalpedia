-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P33_normalStatesEpsilonDelta
-- name    : QAlgorithms.Papers.Independent.Next46.P33.normalStatesEpsilonDelta
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:28:27.16484+00:00
-- url     : https://prove2.me/theorems/0ab081d3-e6cd-4d95-8106-67230d9a325c
-- title:
--   Normal states are epsilon-delta absolutely continuous
-- statement:
--   Let $M$ be a von Neumann algebra, let $\phi_1$ be a faithful normal state on $M$, and let $\phi_0$ be any normal state on $M$. Then
--
--   $$
--   \forall\varepsilon>0\;\exists\delta>0\;\forall e\in\operatorname{Proj}(M),\qquad
--   \phi_1(e)<\delta\ \Longrightarrow\ \phi_0(e)<\varepsilon.
--   $$
--
--   Here $\operatorname{Proj}(M)$ denotes the self-adjoint projections of $M$. The modulus $\delta$ is uniform over these projections. This identifies the finite-state instance of the paper's absolute-continuity condition.
-- source:
--   Composition Operators on Haagerup $L^p$-spaces, arXiv:math/0603612v2, PDF p. 4, Lemma 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P33

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 3.2, PDF p.4. A normal state is uniformly epsilon-delta absolutely
continuous with respect to a faithful normal state. The other state may be
nonfaithful. -/
theorem normalStatesEpsilonDelta
    (M : VonNeumannAlgebra H) (phi1 phi0 : Weight M)
    (hNormal1 : IsNormalWeight phi1) (hState1 : IsStateWeight phi1)
    (hFaithful1 : IsFaithfulWeight phi1)
    (hNormal0 : IsNormalWeight phi0) (hState0 : IsStateWeight phi0) :
    WeightEpsilonDelta phi0 phi1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P33

end
