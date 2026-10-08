-- Prove2me | Theorems.Thm_RunwayCPS_TotalDelay_min_total_delay_shortest_path
-- name    : RunwayCPS.TotalDelay.min_total_delay_shortest_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:42.625929+00:00
-- url     : https://prove2.me/theorems/14301573-0dc5-4fb0-bb15-53a21024b600
-- title:
--   §5.2 — the minimum total delay without time windows is the shortest source-sink path with arc distances (n − p + 1)δ_i(j)
-- statement:
--   Consider the runway problem of §5.2: $n$ aircraft labelled in FCFS order, a maximum position shift $k$, a finite set of precedence pairs $(x,y)$ with $x\ne y$ ($x$ must land before $y$), and separations $\delta_{ab}\ge0$ satisfying the triangle inequality $\delta_{ac}\le\delta_{ab}+\delta_{bc}$, with **no time windows**. A feasible schedule is a $k$-CPS sequence $\sigma$ respecting the precedence pairs with landing times $t_p\ge0$ such that $t_q-t_p\ge\delta_{\sigma(p)\sigma(q)}$ for all positions $p<q$. Its total delay is $t_1+\dots+t_n$.
--
--   Let $G$ be the precedence-pruned CPS network, and give the arc $(i,j)$ from stage $p-1$ to stage $p$ the distance $(n-p+1)\delta_i(j)$, with source and sink arcs of distance $0$. Then:
--
--   1. a feasible schedule exists if and only if $G$ has a source-sink path;
--   2. for every real number $D$, $D$ is the minimum total delay over feasible schedules if and only if $D$ is the length of a shortest source-sink path of $G$:
--   $$\min_{(\sigma,t)\ \text{feasible}}\ \sum_{p=1}^{n}t_p\;=\;\min_{v\ \text{source-sink path of }G}\ \sum_{p=2}^{n}(n-p+1)\,\delta_{v_{p-1}}(v_p),$$
--   where each minimum exists exactly when the other does.
--
--   This is the result of §5.2: minimizing the total (equivalently, average) delay under constrained position shifting reduces to a shortest-path problem on the CPS network, whose size is polynomial in $n$ for fixed $k$.
--
--   **Formalization Note** Positions and aircraft are 0-based `Fin n` and stages 0-based, so the arc into stage $s$ has distance $(n-s)\delta_i(j)$. Delay is measured from time $0$, with all aircraft available then, which is encoded as $t_p\ge0$. The paper fixes no time origin, but its path length equals the total delay exactly under this convention, and without a lower bound on the times no minimum exists. Separations are required between every pair of aircraft, not only consecutive ones. The two minima are compared with `IsLeast`, and part 1 is stated separately because part 2 alone does not force either minimum to exist. The paper's precedence pairs always consist of two distinct aircraft, hence the hypothesis $x\ne y$. For $n=0$ both minima are $0$.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1656, §5.2, last two paragraphs (shortest-path equivalence), with §5.2 opening paragraph (p. 1655) for the problem

import Mathlib
import Definitions.Def_RunwayCPS_TotalDelay_Network

namespace RunwayCPS.TotalDelay

theorem min_total_delay_shortest_path {n : ℕ} (I : Instance n)
    (hδ : ∀ a b : Fin n, 0 ≤ I.δ a b)
    (htri : ∀ a b c : Fin n, I.δ a c ≤ I.δ a b + I.δ b c)
    (hprec : ∀ x y : Fin n, (x, y) ∈ I.prec → x ≠ y) :
    ((∃ (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ), IsFeasible I σ t) ↔
        ∃ v : ℕ → List (Fin n), IsPathIn I v) ∧
    ∀ D : ℝ,
      IsLeast {x : ℝ | ∃ (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ),
          IsFeasible I σ t ∧ x = totalDelay t} D ↔
        IsLeast {x : ℝ | ∃ v : ℕ → List (Fin n), IsPathIn I v ∧ x = pathLength I v} D := by sorry

end RunwayCPS.TotalDelay
