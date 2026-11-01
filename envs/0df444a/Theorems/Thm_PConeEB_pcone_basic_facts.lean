-- Prove2me | Theorems.Thm_PConeEB_pcone_basic_facts
-- name    : PConeEB.pcone_basic_facts
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:59.553056+00:00
-- url     : https://prove2.me/theorems/97b278c4-87d0-4077-8511-0daf3aff9fc4
-- title:
--   §4 after (4.1) — dual, pointedness and full dimension of $\mathcal K_p^{n+1}$
-- statement:
--   Let $n\ge2$, $p,q\in(1,\infty)$ with $\frac1p+\frac1q=1$. Then the dual cone of $\mathcal K_p^{n+1}$, for the usual Euclidean inner product, is $\mathcal K_q^{n+1}$:
--   $$
--   (\mathcal K_p^{n+1})^*=\mathcal K_q^{n+1}.
--   $$
--   Moreover $\mathcal K_p^{n+1}$ is a closed convex cone, it is pointed ($\mathcal K_p^{n+1}\cap-\mathcal K_p^{n+1}=\{0\}$), and it is full-dimensional (its linear span is $\mathbb R^{n+1}$).
--
--   These facts place the $p$-cone in the general framework: the exposing vectors of its faces are points of the $q$-cone.
--
--   Differences from the source:
--   - encoding: a pointed full-dimensional cone → IsClosedConvexCone (published MoreauProx.Decomposition), K ∩ -K = {0} and Submodule.span ℝ K = ⊤; reason: "cone" in §2 means closed convex cone; the clauses spell out the same facts
--   - encoding: ℝ^{n+1}, x₀, x̄, ‖x̄‖_p, ∂ → RR n = EuclideanSpace ℝ (Fin (n + 1)), x 0, x i.succ for i : Fin n, pNorm with real rpow, frontier; reason: Lean conventions; same instances
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, §4, after (4.1), p.17

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_pCone

open MoreauProx.Decomposition (IsClosedConvexCone)

namespace PConeEB

/-- The basic facts on the `p`-cone quoted after (4.1): the dual cone of `K_p^{n+1}` is `K_q^{n+1}`,
where `1/p + 1/q = 1`, and `K_p^{n+1}` is a pointed full-dimensional closed convex cone.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, §4, after (4.1), p.17.

**Formalization Note.** Pointed is `K ∩ -K = {0}`, and full-dimensional is `span K = ⊤`. -/
theorem pcone_basic_facts {n : ℕ} (hn : 2 ≤ n) {p q : ℝ} (hp : 1 < p)
    (hpq : 1 / p + 1 / q = 1) :
    ((ProperCone.innerDual (pCone n p) : ProperCone ℝ (RR n)) : Set (RR n)) = pCone n q ∧
      IsClosedConvexCone (pCone n p) ∧
      {x | x ∈ pCone n p ∧ -x ∈ pCone n p} = {0} ∧
      Submodule.span ℝ (pCone n p) = ⊤ := by sorry

end PConeEB
