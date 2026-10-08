-- Prove2me | Theorems.Thm_RunwayCPS_TotalDelay_dp_recursion
-- name    : RunwayCPS.TotalDelay.dp_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:02.063991+00:00
-- url     : https://prove2.me/theorems/4ec5f683-a6e9-4c79-89f2-5c9c7c9dd2d9
-- title:
--   §5.2, displayed recursion — θ*_j(p) = min over predecessors i of θ*_i(p − 1) + (n − p + 1)δ_i(j)
-- statement:
--   Consider the runway problem of §5.2 without time windows, with separations $\delta_{ab}\ge0$ satisfying the triangle inequality $\delta_{ac}\le\delta_{ab}+\delta_{bc}$, and let $G$ be the precedence-pruned CPS network. For a node $j$ of $G$ in stage $p$, let $\Theta_j(p)$ be the set of values
--   $$\theta_j(p)=t_1+\dots+t_{p-1}+(n-p+1)\,t_p$$
--   over all partial schedules ending at $j$: paths $v_1,\dots,v_p=j$ in $G$ from the source to $j$, with times $t_q\ge0$ for the final aircraft of their nodes, pairwise separated as required. Let $\theta^*_j(p)=\min\Theta_j(p)$, and let $P(j)$ be the set of predecessors of $j$ in $G$. Then:
--
--   1. (boundary) for every node $j$ of $G$ in stage $1$, $\theta^*_j(1)=0$;
--   2. (recursion) for every node $j$ of $G$ in a stage $p\in\{2,\dots,n\}$,
--   $$\theta^*_j(p)=\min_{i\in P(j)}\Big(\theta^*_i(p-1)+(n-p+1)\,\delta_i(j)\Big),$$
--   in the sense that a real number $m$ is the least element of $\Theta_j(p)$ if and only if it is the least element of $\{\theta^*_i(p-1)+(n-p+1)\delta_i(j)\ :\ i\in P(j),\ \Theta_i(p-1)\text{ has a least element }\theta^*_i(p-1)\}$.
--
--   This is the dynamic programming recursion of §5.2. Iterated from stage $1$ to stage $n$, it computes the minimum total delay as the minimum of $\theta^*_j(n)$ over the nodes $j$ of the last stage.
--
--   **Formalization Note** The paper prints $\theta^*_j(s)$ on the left-hand side; it means $\theta^*_j(p)$. The boundary value $\theta^*_j(1)=0$ is not printed. It corresponds to the zero-length source arcs of the shortest-path formulation, and it holds because the first aircraft may land at time $0$. The minimum is stated with `IsLeast` on both sides, so neither side presupposes that a minimum exists. Stages are 0-based: the paper's stage $p$ is stage $s=p-1$, and the coefficient $n-p+1$ is $n-s$. Predecessors in $G$ are the nodes $i$ of $G$ in the previous stage with an arc $(i,j)$. Nodes unreachable from the source or sink are kept, which does not change any least element.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1655–1656, §5.2, definition of θ_i(p) and θ*(·), and the displayed dynamic programming recursion

import Mathlib
import Definitions.Def_RunwayCPS_TotalDelay_Network

namespace RunwayCPS.TotalDelay

theorem dp_recursion {n : ℕ} (I : Instance n)
    (hδ : ∀ a b : Fin n, 0 ≤ I.δ a b)
    (htri : ∀ a b c : Fin n, I.δ a c ≤ I.δ a b + I.δ b c) :
    (∀ j : List (Fin n), IsNodeG I 0 j → IsLeast (thetaSet I 0 j) 0) ∧
    (∀ (s : ℕ) (j : List (Fin n)), 1 ≤ s → s < n → IsNodeG I s j → ∀ m : ℝ,
      IsLeast (thetaSet I s j) m ↔
        IsLeast {θ : ℝ | ∃ (i : List (Fin n)) (θ' : ℝ), IsNodeG I (s - 1) i ∧
            IsArc I.k (s - 1) i j ∧ IsLeast (thetaSet I (s - 1) i) θ' ∧
            θ = θ' + ((n : ℝ) - (s : ℝ)) * nodeDelta I i j} m) := by sorry

end RunwayCPS.TotalDelay
