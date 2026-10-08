-- Prove2me | Theorems.Thm_WhittFLT_Reflection_barrier_continuous
-- name    : WhittFLT.Reflection.barrier_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:57.012163+00:00
-- url     : https://prove2.me/theorems/243beb49-4111-49c4-ab16-6a1098e4726f
-- title:
--   §6, proof of Theorem 6.4(i), p. 81 — the barrier map is J₁-continuous
-- statement:
--   Let $T$ be a real interval with closed left endpoint $0$, and let $f(x)=x-x^{\downarrow}$ be the reflecting-barrier map. For real càdlàg paths $x_n,x$ on $T$,
--
--   $$
--   x_n\to x\text{ in }J_1\quad\Longrightarrow\quad f(x_n)\to f(x)\text{ in }J_1.
--   $$
--
--   This is the continuity claim made in the proof of Theorem 6.4(i).
--
--   **Formalization Note** The source calls $f$ continuous in each Skorohod topology; this item records the $J_1$ case needed here. The paper’s $T$ is an interval with $0$ as closed left endpoint, made explicit. Paths are total functions on $\mathbb R$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §6, proof of Theorem 6.4(i), p. 81

import Mathlib
import Definitions.Def_WhittFLT_Reflection_Supremum

namespace WhittFLT.Reflection

open Set Filter Topology

/-- Whitt (1980), proof of Theorem 6.4(i), p. 81: the barrier map is J₁-continuous. -/
theorem barrier_continuous (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (hconv : WhittFLT.Composition.J1Tendsto T xs x) :
    WhittFLT.Composition.J1Tendsto T (fun n => barrier (xs n)) (barrier x) := by sorry

end WhittFLT.Reflection
