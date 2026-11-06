-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_dual_isSelfScaledBarrier
-- name    : SelfScaledLongStep.PrimalDual.dual_isSelfScaledBarrier
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T13:58:18.785232+00:00
-- url     : https://prove2.me/theorems/5be411eb-8dfa-4254-a36e-a7cb26fe51fd
-- title:
--   §2 p. 3 (T*2.4.4) and Proposition 3.1, p. 8 — K* is proper and F* is a ν-self-scaled barrier for K*
-- statement:
--   Let $K\subset E=\mathbb R^n$ be a proper cone (closed, convex, pointed, with nonempty interior), let $F$ be a $\nu$-self-scaled barrier for $K$ (Definition 2.1), and let
--   $$F_*(s)=\sup\{-\langle s,x\rangle-F(x):x\in\operatorname{int}K\}$$
--   be its conjugate barrier on the dual cone $K^*=\{s:\langle s,x\rangle\ge0\ \forall x\in K\}$ (2.6). Then:
--
--   1. $K^*$ is again a proper cone (closed, convex, pointed, with nonempty interior);
--   2. $F_*$ is a $\nu$-self-scaled barrier for $K^*$: it is a $\nu$-self-concordant logarithmically homogeneous (nondegenerate) barrier for $K^*$, and for all $u,s\in\operatorname{int}K^*$,
--   $$F_*''(u)s\in\operatorname{int}K^{**}=\operatorname{int}K,\qquad (F_*)_*\big(F_*''(u)s\big)=F_*(s)-2F_*(u)-\nu .$$
--
--   This is the primal–dual symmetry of self-scaled barriers stated on p. 3 (via T*2.4.4 of Nesterov–Nemirovskii: $F_*$ is a $\nu$-self-concordant logarithmically homogeneous barrier for $K^*$, and $K^*$ is pointed with nonempty interior) and in Proposition 3.1, p. 8, (3.3): $F(F_*''(u)s)=F_*(s)-2F_*(u)-\nu$; the conjugate of $F_*$ over $\operatorname{int}K^*$ equals $F$ on $\operatorname{int}K$. It lets every result stated for the primal pair $(K,F)$ be applied verbatim to the dual pair $(K^*,F_*)$, which the paper does throughout ("the corresponding statements for the dual case have an absolutely symmetric form").
--
--   **Formalization Note** The conclusion is `IsProperCone (dualCone K) ∧ IsSelfScaledBarrier (dualCone K) (conj K F) ν` with the same definitions as for the primal side, so the conjugate of the conjugate is `conj (dualCone K) (conj K F)`; $E^*$ is identified with $E$ through the Euclidean inner product.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42: p. 3 (§2, K* pointed with nonempty interior; F* is a ν-self-concordant logarithmically homogeneous barrier for K* by T*2.4.4 of Nesterov–Nemirovskii 1994), and p. 8, Proposition 3.1, (3.3)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Dual symmetry of self-scaled barriers** (p. 3, via T*2.4.4 of Nesterov–Nemirovskii, and
Proposition 3.1, p. 8). If `F` is a `ν`-self-scaled barrier for the proper cone `K`, then the dual
cone `K*` is proper and the conjugate barrier `F* = conj K F` is a `ν`-self-scaled barrier for
`K*`. -/
theorem dual_isSelfScaledBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν) :
    IsProperCone (ConvexOptimization.dualCone K) ∧
      IsSelfScaledBarrier (ConvexOptimization.dualCone K) (conj K F) ν := by sorry

end SelfScaledLongStep.PrimalDual
