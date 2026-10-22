-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P50_gauge_cocycle_identities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P50.gauge_cocycle_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:20:50.41588+00:00
-- url     : https://prove2.me/theorems/6a3225f6-f799-45d7-85b8-414b572e80bb
-- title:
--   The components of a gauge representation satisfy cocycle identities
-- statement:
--   Let $G$ be a group and $H_0$ a complex Hilbert space. Suppose $g\mapsto(D_g,a_g,b_g)$ is an identity-preserving homomorphism into the gauge multiplication (23), with $D_g$ unitary, $a_g\in H_0$, and $b_g\in\mathbb R$. Then $D_1=I$, $a_1=0$, $b_1=0$, and for every $g',g\in G$,
--
--   $$D_{g'g}=D_{g'}D_g,\qquad a_{g'g}=D_{g'}a_g+a_{g'},$$
--
--   $$b_{g'}+b_g-b_{g'g}=\operatorname{Im}\langle a_{g'},D_{g'}a_g\rangle.$$
--
--   Thus the unitary component is a representation, the displacement is a first-order cocycle, and the real component satisfies the stated coboundary equation. This assertion uses only the explicit multiplication and does not assume Theorem 1's deferred existence or continuity claims.
-- source:
--   Covariant Quantum Dynamical Semigroups: Unbounded generators, arXiv:quant-ph/9701037v1, PDF p. 9, §4: component representation, cocycle and coboundary identities

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P50

open scoped TensorProduct BigOperators

variable {H N : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

/-- Holevo, arXiv:quant-ph/9701037v1, PDF p.9, paragraph following Theorem 1.
For a genuine homomorphism into the explicitly defined gauge multiplication,
its unitary component is a representation, its displacement is a cocycle,
and its real component satisfies the printed coboundary equation. -/
theorem gauge_cocycle_identities {G : Type*} [Group G]
    (F : G → NoiseGauge N) (hOne : F 1 = gaugeIdentity)
    (hMul : ∀ gp g, F (gp * g) = gaugeMul (F gp) (F g)) :
    (F 1).Dnoise = LinearIsometryEquiv.refl ℂ N ∧
    (F 1).a = 0 ∧ (F 1).b = 0 ∧
    ∀ gp g,
      (F (gp * g)).Dnoise = (F g).Dnoise.trans (F gp).Dnoise ∧
      (F (gp * g)).a = (F gp).Dnoise (F g).a + (F gp).a ∧
      (F gp).b + (F g).b - (F (gp * g)).b =
        (inner ℂ (F gp).a ((F gp).Dnoise (F g).a)).im := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P50

end
