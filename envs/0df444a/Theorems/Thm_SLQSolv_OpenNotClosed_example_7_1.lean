-- Prove2me | Theorems.Thm_SLQSolv_OpenNotClosed_example_7_1
-- name    : SLQSolv.OpenNotClosed.example_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:29.905681+00:00
-- url     : https://prove2.me/theorems/53e6c8b6-e398-4cd3-93f5-18acd93c2cd5
-- title:
--   Example 7.1, pp. 2305–2306 — open-loop solvable at every (t, x), value discontinuous at t = 1, closed-loop solvable on no [t, 1]
-- statement:
--   Consider Problem (SLQ)$^0$ with the one-dimensional state equation (7.1) and the cost (7.2):
--
--   $$
--   dX(s)=[u_1(s)+u_2(s)]ds+[u_1(s)-u_2(s)]dW(s),\quad s\in[t,1],\qquad X(t)=x,\qquad J^0(t,x;u(\cdot))=\mathbb EX(1)^2,
--   $$
--
--   where $u=(u_1,u_2)^\top$ ranges over $\mathcal U[t,1]$, on an arbitrary probability space carrying a standard Brownian motion $W$ with its augmented filtration. Then:
--
--   1. for every $(t,x)\in[0,1)\times\mathbb R$ the control (7.11)
--   $$
--   u^*_{(t,x)}(s)=-\Big(\frac{x}{2-2t},\frac{x}{2-2t}\Big)^\top,\qquad t\le s\le1,
--   $$
--   is an open-loop optimal control, so the problem is open-loop solvable on $[0,1)\times\mathbb R$;
--   2. the value function is (7.8): $V^0(t,x)=0$ for $0\le t<1$ and $V^0(1,x)=x^2$ for all $x\in\mathbb R$; in particular it is not continuous in $t$;
--   3. for every $t\in[0,1)$ the problem is not closed-loop solvable on $[t,1]$.
--
--   This is the paper's counterexample to the necessity part of Theorem 4.2 (Ait Rami, Moore and Zhou): the problem has a continuous open-loop optimal control at every initial pair, yet its Riccati equation has no regular solution. It shows that open-loop and closed-loop solvability are different notions.
--
--   **Formalization Note** The control $u^*$ is constant in $(s,\omega)$, so its continuity in $s$ is automatic and not stated. Closed-loop optimality requires, for every initial state, a solution of the closed-loop system (2.4); failure of closed-loop solvability is stated for each $[t,1]$ separately, not merely for some interval. No assumption is made on the probability space beyond the Brownian motion.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §7 first paragraph and Example 7.1, (7.1)–(7.2), (7.8), (7.11), pp. 2305–2306

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Examples

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

/-- Example 7.1, pp. 2305–2306: Problem (SLQ)⁰ with `dX = [u₁ + u₂] ds + [u₁ − u₂] dW`, `J⁰ = E X(1)²`
is open-loop solvable at every `(t, x) ∈ [0, 1) × ℝ` with the optimal control
`u* = −(x/(2 − 2t), x/(2 − 2t))ᵀ` (7.11); its value function is `V⁰(t, x) = 0` for `t < 1` and
`V⁰(1, x) = x²` (7.8); and it is closed-loop solvable on no `[t, 1]`, `t < 1`. -/
theorem example_7_1 {Ω : Type*} [MeasurableSpace Ω] (Bs : Basis Ω) :
    (∀ t : ℝ≥0, t < 1 → ∀ x : Fin 1 → ℝ,
      IsOpenLoopOptimal Bs (ex71 (Ω := Ω)) t x
        (fun _ _ => ![-(x 0) / (2 - 2 * (t : ℝ)), -(x 0) / (2 - 2 * (t : ℝ))])) ∧
    (∀ t : ℝ≥0, t < 1 → ∀ x : Fin 1 → ℝ, V0 Bs (ex71 (Ω := Ω)) t x = 0) ∧
    (∀ x : Fin 1 → ℝ, V0 Bs (ex71 (Ω := Ω)) 1 x = ((x 0 ^ 2 : ℝ) : EReal)) ∧
    ∀ t : ℝ≥0, t < 1 → ¬ ClosedLoopSolvableOn Bs (ex71 (Ω := Ω)) t := by sorry

end SLQSolv.OpenNotClosed
