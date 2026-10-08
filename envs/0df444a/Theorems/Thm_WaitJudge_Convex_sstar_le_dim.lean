-- Prove2me | Theorems.Thm_WaitJudge_Convex_sstar_le_dim
-- name    : WaitJudge.Convex.sstar_le_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:57:48.978608+00:00
-- url     : https://prove2.me/theorems/868f86c6-afd1-4922-828b-60be6409409f
-- title:
--   Sect. 1, p. 4 (from [7]) and Sect. 5.1.1, p. 13 — a convex scenario program has at most d support constraints
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$ and every $\mathcal X_\delta$ be convex, let the tie-break functions $t_1,\dots,t_p$ be convex, and let Assumption 1 hold: every scenario program (9), for every sample size $m$ and every sample, has a unique tie-broken solution. Then for every $m$ and every sample $\delta^{(1)},\dots,\delta^{(m)}$ the number of support constraints satisfies
--   $$s^*_m\le d.$$
--
--   The bound says that the number of support constraints never exceeds the number of optimization variables. It is what allows the probability of $V(x^*_N)>\epsilon(s^*_N)$ to be split into the $d+1$ events $s^*_N=k$, $k=0,\dots,d$, in (13).
--
--   **Formalization Note** The paper quotes this fact from Calafiore and Campi (2005). A support constraint is one whose removal changes the tie-broken solution. The statement is deterministic: no measure appears.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 4 (paragraph after Definition 2, citing [7]) and PDF p. 13 (before (13))

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization

namespace WaitJudge.Convex

theorem sstar_le_dim {d p : ℕ} {Δ : Type*} (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d))
    (tb : Fin p → E d → ℝ) (hX : Convex ℝ X) (hXδ : ∀ δ, Convex ℝ (Xδ δ))
    (htb : ∀ j, ConvexOn ℝ Set.univ (tb j)) (hA1 : Assumption1 c X Xδ tb) :
    ∀ (m : ℕ) (ω : Fin m → Δ), sstar c X Xδ tb ω ≤ d := by sorry

end WaitJudge.Convex
