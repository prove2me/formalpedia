-- Prove2me | Theorems.Thm_ProxAlg_FixedPoint_prox_optimality
-- name    : ProxAlg.FixedPoint.prox_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:05.385989+00:00
-- url     : https://prove2.me/theorems/65d426e4-f746-40e4-bc6a-f82bf46417f0
-- title:
--   §2.3, p. 131 — proximal minimizers satisfy the subdifferential optimality condition
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be closed, proper and convex, and let $v,x\in\mathbb R^n$. Write $\partial f(x)$ for the subdifferential defined by (2.3). Then
--   $$
--   x=\operatorname{prox}_f(v)\quad\Longleftrightarrow\quad 0\in\partial f(x)+(x-v),
--   $$
--   equivalently, $v-x\in\partial f(x)$.
--
--   This characterizes the proximal minimizer through a first-order condition and supplies the link between proximal maps and subdifferentials.
--
--   **Formalization Note** The proximal point is expressed by Moreau's `IsProx` predicate, which minimizes $\tfrac12\|u-v\|_2^2+f(u)$ and has a unique solution under the stated hypotheses. The paper's subdifferential is the local definition from (2.3).
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §2.3, p. 131, proof following the fixed-point statement

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_ProxAlg_FixedPoint_Basic

namespace ProxAlg.FixedPoint

theorem prox_optimality {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : MoreauProx.Decomposition.GammaZero f)
    (v x : EuclideanSpace ℝ (Fin n)) :
    MoreauProx.Decomposition.IsProx f v x ↔ v - x ∈ subdifferential f x := by sorry

end ProxAlg.FixedPoint
