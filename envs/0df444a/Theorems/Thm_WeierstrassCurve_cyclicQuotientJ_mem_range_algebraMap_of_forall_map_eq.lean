-- Prove2me | Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq
-- name    : WeierstrassCurve.cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/58aa2862-5c3f-597d-8fe8-2b34c6444b32
-- title:
--   Rationality of j(E/H) for Galois-stable cyclic H
-- statement:
--   Let $F$ be a field and $E$ a Weierstrass curve over $F$ satisfying `IsElliptic`, and let $K$ be an algebraically closed field that is an $F$-algebra and algebraic over $F$. Let $N \geq 1$ and let `data` be a `ModularPolynomialData N`, that is, a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic in $Y$, of degree $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ in $Y$, and which vanishes when $X$ is replaced by the Laurent series $j(q)$ and $Y$ by $j(q^N)$ over $\mathbb{Q}$. Assume $N \neq 0$ in $K$ and that the polynomial in $K[Y]$ obtained from $\Phi$ by applying to each coefficient the evaluation $\mathbb{Z}[X] \to K$ sending $X$ to the image of $j(E)$ under $F \to K$ is separable. Let $H$ be a subgroup of the group of affine points of the base change of $E$ to $K$ such that $H$ is cyclic with $\operatorname{card} H = N$, and such that for every $F$-algebra automorphism $\sigma$ of $K$ the image of $H$ under the induced map on points is again $H$. Then `cyclicQuotientJ` of the base change of $E$ to $K$ at $H$ and $N$, namely $c_4^3/\Delta$ of the Weierstrass curve produced by the iteration `cqjIterate`, lies in the image of $F \to K$.
--
--   This is the rationality over the base field of the $j$-invariant of the quotient of an elliptic curve by a cyclic subgroup stable under the absolute Galois action, with the separability of the specialised modular polynomial $\Phi_N(j(E),Y)$ imposed as a hypothesis. It feeds the construction of rigid data in [`WeierstrassCurve.DrinfeldGlobal.exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_algebraMap_eq_cyclicQuotientJ_of_raw_rigidDataPow), where cyclic isogeny quotients defined over $K$ must be recognised as coming from the ground field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve

universe u v in

theorem WeierstrassCurve.cyclicQuotientJ_mem_range_algebraMap_of_forall_map_eq
    {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]
    (K : Type v) [Field K] [DecidableEq K] [IsAlgClosed K] [Algebra F K] [Algebra.IsAlgebraic F K]
    (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (hN : (N : K) ≠ 0)
    (hsep : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K)
      (algebraMap F K E.j))).Separable)
    (H : AddSubgroup (E.baseChange K).toAffine.Point) (hH : IsAddCyclic H ∧ Nat.card H = N)
    (hstab : ∀ σ : K ≃ₐ[F] K,
      H.map (WeierstrassCurve.Affine.Point.map (σ : K →ₐ[F] K)) = H) :
    (E.baseChange K).cyclicQuotientJ H N ∈ (algebraMap F K).range := by sorry
