-- Prove2me | Theorems.Thm_PolylogKServer_Rounding_online_rounding
-- name    : PolylogKServer.Rounding.online_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:09:42.351186+00:00
-- url     : https://prove2.me/theorems/80c9fd83-738e-46a7-a518-7c37391d1de9
-- title:
--   Theorem 24 — online rounding of fractional k-server states on a σ-HST (σ > 5) at cost O(c_t) per step
-- statement:
--   For every $\sigma>5$ there is a constant $C>0$ such that the following holds. Let $T$ be a $\sigma$-HST whose leaves form the finite metric space $M$, and let $C_0$ be a configuration of $k$ leaves. There is an online procedure that, given the fractional states $x^0,\dots,x^t$ seen so far, outputs a k-server state $S_t$, such that for every sequence $x^0,x^1,\dots$ of fractional k-server states with $x^0$ the indicator of $C_0$:
--
--   1. $S_0$ is the point mass on $C_0$, and at any time $t$ the state $S_t$ is consistent with $x^t$;
--   2. if the fractional state changes from $x^{t-1}$ to $x^t$, incurring a movement cost of $c_t=\sum_{v\neq r}W(v)\,|x^t_v-x^{t-1}_v|$, then the cost of changing $S_{t-1}$ to $S_t$ is at most $C\,c_t$.
--
--   Theorem 7 follows from it: the rounded states define a randomized k-server algorithm whose cost is within a constant factor of the fractional cost.
--
--   **Formalization Note** The procedure is online because $S_t$ is a function of $x^0,\dots,x^t$ only. The start $x^0$ is integral (the indicator of $C_0$), the case Theorem 7 uses; the paper's proof starts from a state $S_0$ consistent and balanced with respect to $x^0$. The $O(\cdot)$ is a constant depending on $\sigma$ only. The cost of changing a state is the transportation cost of `PolylogKServer.Rounding.States`.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 36, Theorem 24

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Fractional_KServer
import Definitions.Def_PolylogKServer_Rounding_States

namespace PolylogKServer.Rounding

open PolylogKServer.HST PolylogKServer.Fractional

/-- **Theorem 24** (arXiv:1110.1580v1, p. 36). For every `σ > 5` there is a constant `C > 0`
(depending on `σ` only) such that for every σ-HST `T` whose leaves form the metric space `M`,
every `k` and every `k`-subset `C₀` of the leaves there is an online procedure `P`, mapping the
fractional states `x⁰, …, x^t` seen so far to a k-server state `S_t = P [x⁰, …, x^t]`, such that
for every sequence `x⁰, x¹, …` of fractional k-server states starting at the indicator of `C₀`:
`S₀` is the point mass at `C₀`; every `S_t` is a k-server state consistent with `x^t`; and the
cost of changing `S_{t−1}` to `S_t` is at most `C · c_t`, where `c_t` is the movement cost of
the fractional state from `x^{t−1}` to `x^t`. -/
theorem online_rounding :
    ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] [DecidableEq M] (e : M ≃ T.Leaf),
        T.IsLeafMetric M e →
      ∀ (k : ℕ) (C₀ : KConfig k M),
        ∃ P : List (M → ℝ) → (KConfig k M → ℝ),
          ∀ xs : ℕ → M → ℝ, (∀ t, IsFracState k (xs t)) →
            xs 0 = (fun m => if m ∈ C₀.1 then 1 else 0) →
            P [xs 0] = pureState C₀ ∧
            (∀ t, IsKState (P ((List.range (t + 1)).map xs)) ∧
              Consistent (P ((List.range (t + 1)).map xs)) (xs t)) ∧
            ∀ t, transportCost (P ((List.range (t + 1)).map xs))
                (P ((List.range (t + 2)).map xs)) ≤
              C * fracMoveCost T e (xs t) (xs (t + 1)) := by sorry

end PolylogKServer.Rounding
