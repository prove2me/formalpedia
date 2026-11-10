-- Prove2me | Theorems.Thm_TaoCake_Impossibility_theorem_3_1
-- name    : TaoCake.Impossibility.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:07:48.096255+00:00
-- url     : https://prove2.me/theorems/86a4c99e-0f24-4dc6-9736-bb040433fffa
-- title:
--   Theorem 3.1 — no truthful proportional cake-cutting mechanism for two hungry agents with piecewise-constant densities, even without entireness
-- statement:
--   Consider dividing the cake $C = [0,1]$ between **two agents**. Each agent $i$ has a **value density** $f_i : [0,1] \to \mathbb R$ that is **piecewise-constant** ($[0,1]$ is partitioned into finitely many intervals, with $f_i$ constant on each; the number of intervals, their endpoints and the real levels are arbitrary) and **hungry**: $f_i(x) > 0$ for every $x \in [0,1]$. The utility of a set $X$ is $v_i(X) = \int_{X} f_i(x)\,dx$. A deterministic **mechanism** $M$ maps every reported profile $F = (f_1, f_2)$ of such densities to an **allocation** $(M_1(F), M_2(F))$: two disjoint measurable subsets of $[0,1]$, not necessarily covering the cake. $M$ is **proportional** if $v_i(M_i(F)) \ge \tfrac12 v_i([0,1])$ for every profile $F$ and agent $i$ (measured with the reported density), and **truthful** if no agent can gain by a unilateral misreport: for every profile $F$, every agent $i$ and every admissible report $g$,
--
--   $$\int_{M_i(F)} f_i(x)\,dx \;\ge\; \int_{M_i(F[i \leftarrow g])} f_i(x)\,dx .$$
--
--   **Theorem 3.1** (p. 4). There is no mechanism that is both truthful and proportional, even when there are two agents, each value density is piecewise-constant and hungry, and the mechanism need not be entire.
--
--   This answers the question, raised by Chen, Lai, Parkes and Procaccia (2010) and repeated by Procaccia, Aziz–Ye, Brânzei–Miltersen, Menon–Larson and Bei et al., whether a deterministic, truthful and envy-free, or even proportional, cake-cutting mechanism exists. Since every entire envy-free allocation is proportional, it also rules out deterministic truthful envy-free mechanisms that output entire allocations.
--
--   **Formalization Note** Agents are `Fin 2`; Lean agent `0` is the paper's agent 1. `Mechanism` is a raw map on all pairs of real functions; `IsFeasible`, `IsTruthful` and `IsProportional` (module `TaoCake.Impossibility.Model`) constrain it only at profiles of admissible densities and over admissible misreports, which is equivalent to the paper's mechanism on its domain. Output pieces are arbitrary Lebesgue-measurable subsets of $[0,1]$, so the excluded class includes every mechanism of the paper.
--
--   Differences from the source:
--   - generalization: allocation pieces are subsets of [0,1] whose utilities are the Riemann integrals ∫_X f_i(x) dx → pieces are arbitrary Lebesgue-measurable (NullMeasurableSet) pairwise disjoint subsets of [0,1]; utility is the Lebesgue integral of f over X ∩ [0,1]; reason: every set whose Riemann utility exists for a hungry piecewise-constant density is Lebesgue measurable with the same integral, so every source mechanism is covered; quantifying over more mechanisms specializes to the source
--   - encoding: a mechanism maps profiles of piecewise-constant hungry densities f_i : [0,1] → ℝ≥0 to allocations → a Mechanism is a function on all pairs of real functions ℝ → ℝ; feasibility, truthfulness (over admissible misreports) and proportionality are required only at profiles of admissible densities; utility ignores values off [0,1], although the raw mechanism may depend on them; reason: mechanism existence is equivalent for this representation: extend a source mechanism by restricting reports to [0,1], with arbitrary outputs only at inadmissible profiles; conversely restrict a Lean mechanism to reports extended by zero outside [0,1]; unilateral replacement commutes with these choices
--   - encoding: agents 1 and 2 → agents 0 and 1 of Fin 2; reason: Lean indexing; Lean agent 0 is the paper's agent 1
--   - encoding: [0,1] can be partitioned into finitely many intervals with f constant on each → a family I : Fin n → Set ℝ of pairwise disjoint order-connected sets with union [0,1] and f constant on each I k; reason: order-connected subsets of ℝ are exactly the intervals (including degenerate and empty ones); same densities
-- source:
--   Biaoshuai Tao, On Existence of Truthful Fair Cake Cutting Mechanisms, arXiv:2104.07387v1, p. 4 (PDF 4), Theorem 3.1

import Mathlib
import Definitions.Def_TaoCake_Impossibility_Model
import Definitions.Def_TaoCake_Impossibility_Instances

open MeasureTheory

namespace TaoCake.Impossibility

/-- Theorem 3.1 (arXiv:2104.07387v1, p. 4): there is no truthful proportional mechanism for two
agents with piecewise-constant hungry value densities, even when the mechanism need not be
entire. -/
theorem theorem_3_1 :
    ¬ ∃ M : Mechanism, IsFeasible M ∧ IsTruthful M ∧ IsProportional M := by sorry

end TaoCake.Impossibility
