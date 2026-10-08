-- Prove2me | Theorems.Thm_WhittFLT_Reflection_theorem_6_2
-- name    : WhittFLT.Reflection.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:40.090045+00:00
-- url     : https://prove2.me/theorems/80160af7-9f93-4170-93fb-e7207053e601
-- title:
--   Theorem 6.2 — running supremum of linearly centered paths
-- statement:
--   Let $T$ be a real interval with closed left endpoint $0$. Let $x_n,x\in D(T,\mathbb R)$ and $c_n\in\mathbb R$, and suppose $x_n-c_ne\to x$ in $J_1$, where $e(t)=t$. The running supremum has three drift regimes:
--
--   1. If $c_n\to c$, then $x_n^{\uparrow}\to(x+ce)^{\uparrow}$ in $J_1$.
--   2. If $c_n\to+\infty$ and $x$ has no negative jumps, then $x_n^{\uparrow}-c_ne\to x$ in $J_1$.
--   3. If $c_n\to-\infty$, then $x_n^{\uparrow}\to(t\mapsto x(0))$ uniformly on compact subintervals of $T$.
--
--   This is the source’s trichotomy for the running supremum and supplies the corresponding infimum facts used in Theorem 6.4.
--
--   **Formalization Note** The paper's standing assumptions of §6 ($S=\mathbb R$, $T$ an interval with $0$ as closed left endpoint) are explicit. Membership in $D$ is included in $J_1$ convergence. Paths are total functions on $\mathbb R$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 6.2, p. 80, proof p. 81

import Mathlib
import Definitions.Def_WhittFLT_Reflection_Supremum

namespace WhittFLT.Reflection

open Set Filter Topology

/-- Whitt (1980), Theorem 6.2, pp. 80–81. -/
theorem theorem_6_2 (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : WhittFLT.Composition.J1Tendsto T (fun n t => xs n t - c n * t) x) :
    (∀ c₀ : ℝ, Tendsto c atTop (𝓝 c₀) →
      WhittFLT.Composition.J1Tendsto T (fun n => runSup (xs n)) (runSup (fun t => x t + c₀ * t))) ∧
    (Tendsto c atTop atTop → NoNegJump T x →
      WhittFLT.Composition.J1Tendsto T (fun n t => runSup (xs n) t - c n * t) x) ∧
    (Tendsto c atTop atBot →
      WhittFLT.Composition.UTendsto T (fun n => runSup (xs n)) (fun _ => x 0)) := by sorry

end WhittFLT.Reflection
