-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_variableChange_stabilizer_eq_of_fullKernelQuotient
-- name    : WeierstrassCurve.natCard_variableChange_stabilizer_eq_of_fullKernelQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/3f45060c-312b-5104-b973-11db94a08c18
-- title:
--   Equinumerous variable-change stabilisers along a Vélu cyclic isogeny
-- statement:
--   Let $K$ be an algebraically closed field, let $N$ be a nonzero natural number with $N \neq 0$ in $K$, and let $W$ be a Weierstrass curve over $K$ that is elliptic. Let $Q$ be a point of the affine model of $W$ of exact additive order $N$, and write $W' =$ `W.fullKernelQuotient Q N` for the Vélu quotient model: the Weierstrass curve with the same $a_1, a_2, a_3$ as $W$, with $a_4$ replaced by $a_4 - 5t$ and $a_6$ by $a_6 - b_2 t - 7w$, where, $S$ denoting the finite set of coordinate pairs $(x,y)$ of the points $k \cdot Q$ for $1 \le k \le N-1$ (the point at infinity contributing $(0,0)$), $t = \sum_{(x,y) \in S} (3x^2 + 2a_2x + a_4 - a_1y)$ and $w = \sum_{(x,y) \in S} \bigl(x(3x^2+2a_2x+a_4-a_1y) + y(2y + a_1x + a_3)\bigr)$. Assume $\Delta(W') \neq 0$, and let $\varphi$ be a homomorphism of additive groups from the points of $W$ to the points of $W'$ whose kernel is the subgroup $\langle Q \rangle$ of integer multiples of $Q$ and which, on every point $P \notin \langle Q\rangle$, is given in coordinates by Vélu's translation sums: each coordinate of $\varphi(P)$ is the corresponding coordinate of $P$ plus $\sum_{k=1}^{N-1}$ of the difference of that coordinate of $P + k\cdot Q$ and of $k \cdot Q$. The conclusion equates two cardinalities. The first counts the Weierstrass variable changes $\gamma = (u,r,s,t)$ with $\gamma \cdot W = W$ such that every $T \in \langle Q \rangle$ is carried by the inverse substitution $x \mapsto u^{-2}(x-r)$, $y \mapsto u^{-3}(y - t - s(x-r))$ (a point of $\gamma \cdot W$, compared by heterogeneous equality) to some $T' \in \langle Q\rangle$. The second counts the variable changes $\gamma'$ with $\gamma' \cdot W' = W'$ such that for every $P$ with $N \cdot P = 0$ on $W$ the image of $\varphi(P)$ under the inverse substitution attached to $\gamma'$ equals $\varphi(P')$ for some $P'$ with $N \cdot P' = 0$.
--
--   This is the statement that an automorphism of the pair $(W, \langle Q \rangle)$ descends to the Vélu quotient and that, conversely, automorphisms of the quotient preserving the image $\varphi(W[N])$ of the $N$-torsion lift, so that the two stabilisers have the same order; it is recorded here at the level of variable changes fixing the given Weierstrass model. It feeds the computation of ramification of the $j$-map on modular curves, being used in [`ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard`](thm.html#ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard) and [`ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq`](thm.html#ModularCurve.placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natCard_variableChange_stabilizer_eq_of_fullKernelQuotient.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.natCard_variableChange_stabilizer_eq_of_fullKernelQuotient
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    :
    Nat.card {γ : VariableChange K // γ • W = W ∧
        ∀ T ∈ AddSubgroup.zmultiples Q, ∃ T' ∈ AddSubgroup.zmultiples Q,
          HEq (Point.vcInvFun γ W.toAffine T) T'} =
      Nat.card {γ' : VariableChange K // γ' • (W.fullKernelQuotient Q N) = W.fullKernelQuotient Q N ∧
        ∀ P : W.toAffine.Point, N • P = 0 → ∃ P' : W.toAffine.Point, N • P' = 0 ∧
          HEq (Point.vcInvFun γ' (W.fullKernelQuotient Q N).toAffine (φ P)) (φ P')} := by sorry
