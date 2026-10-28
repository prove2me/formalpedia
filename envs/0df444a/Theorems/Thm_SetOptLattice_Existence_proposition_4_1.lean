-- Prove2me | Theorems.Thm_SetOptLattice_Existence_proposition_4_1
-- name    : SetOptLattice.Existence.proposition_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:41.4958+00:00
-- url     : https://prove2.me/theorems/7f9e336d-bbdb-41c6-b8c6-23c5bb6c75d8
-- title:
--   Proposition 4.1, p. 23 — Weierstrass for extended real-valued φ: compact sublevel sets on (inf φ, r̄] give a minimizer
-- statement:
--   Let $X$ be a separated (Hausdorff) topological linear space over $\mathbb R$ and $\varphi\colon X\to\mathbb R\cup\{\pm\infty\}$. Write $L_\varphi(r)=\{x\in X\mid\varphi(x)\le r\}$. Suppose there is $\bar r\in\mathbb R$ with $\inf_{x\in X}\varphi(x)<\bar r$ such that $L_\varphi(r)$ is compact for every real $r$ with $\inf_{x\in X}\varphi(x)<r\le\bar r$. Then there is $\bar x\in X$ with
--
--   $$\varphi(\bar x)=\inf_{x\in X}\varphi(x).$$
--
--   No semicontinuity of $\varphi$ is assumed, and the infimum may be $-\infty$. The proposition is the scalar existence result that Theorems 4.2 and 4.3 apply to each scalarization $\psi^\triangle\circ f$.
--
--   **Formalization Note** The hypothesis $\inf_X\varphi<\bar r$ is added. The page does not state it, but without it the compactness assumption can be vacuous and the claim fails: for $\varphi(x)=e^x$ on $\mathbb R$ and $\bar r=-1$ no $r$ satisfies $\inf\varphi=0<r\le-1$, and the infimum $0$ is not attained. The Hausdorff property is the paper's standing assumption for §4 (p. 22) and is needed: compact sets must be closed for the intersection argument.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 23, Proposition 4.1; standing assumption of §4, p. 22

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Proposition 4.1, p. 23: a Weierstrass-type theorem for extended real-valued functions. -/
theorem proposition_4_1 {X : Type*}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X]
    (φ : X → EReal) (rbar : ℝ) (hlt : (⨅ x, φ x) < (rbar : EReal))
    (hc : ∀ r : ℝ, (⨅ x, φ x) < (r : EReal) → r ≤ rbar → IsCompact (sublevel φ r)) :
    ∃ xbar : X, φ xbar = ⨅ x, φ x := by sorry

end SetOptLattice.Existence
