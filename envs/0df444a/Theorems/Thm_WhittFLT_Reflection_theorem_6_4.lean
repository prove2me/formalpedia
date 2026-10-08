-- Prove2me | Theorems.Thm_WhittFLT_Reflection_theorem_6_4
-- name    : WhittFLT.Reflection.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:00.338808+00:00
-- url     : https://prove2.me/theorems/182dda44-8b3b-4843-a502-8e9eebba5047
-- title:
--   Theorem 6.4 — reflection of linearly centered paths
-- statement:
--   Let $T$ be a real interval with closed left endpoint $0$. Let $x_n,x\in D(T,\mathbb R)$ and $c_n\in\mathbb R$, suppose $x_n-c_ne\to x$ in $J_1$, and assume $x(0)=0$. For $f(z)=z-z^{\downarrow}$ and $e(t)=t$:
--
--   1. If $c_n\to c$, then $f(x_n)\to f(x+ce)$ in $J_1$.
--   2. If $c_n\to+\infty$, then $f(x_n)-c_ne\to x$ in $J_1$.
--   3. If $c_n\to-\infty$ and $x$ has no positive jumps, then $f(x_n)\to0$ uniformly on compact subintervals of $T$.
--
--   The three conclusions describe how the reflecting barrier behaves under finite, large positive, and large negative linear drifts.
--
--   **Formalization Note** Membership in $D$ is included in the $J_1$ hypothesis. The paper’s standing assumptions that $T$ is an interval, $0$ is its closed left endpoint, and $S=\mathbb R$ are explicit. Paths are total functions on $\mathbb R$; convergence is sequential and uses the extended nonnegative metric. The paper’s $f$ subtracts the entire running infimum.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 6.4, p. 81

import Mathlib
import Definitions.Def_WhittFLT_Reflection_Supremum

namespace WhittFLT.Reflection

open Set Filter Topology

/-- Whitt (1980), Theorem 6.4, p. 81. -/
theorem theorem_6_4 (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : WhittFLT.Composition.J1Tendsto T (fun n t => xs n t - c n * t) x) (hx0 : x 0 = 0) :
    (∀ c₀ : ℝ, Tendsto c atTop (𝓝 c₀) →
      WhittFLT.Composition.J1Tendsto T (fun n => barrier (xs n)) (barrier (fun t => x t + c₀ * t))) ∧
    (Tendsto c atTop atTop →
      WhittFLT.Composition.J1Tendsto T (fun n t => barrier (xs n) t - c n * t) x) ∧
    (Tendsto c atTop atBot → NoPosJump T x →
      WhittFLT.Composition.UTendsto T (fun n => barrier (xs n)) (fun _ => 0)) := by sorry

end WhittFLT.Reflection
