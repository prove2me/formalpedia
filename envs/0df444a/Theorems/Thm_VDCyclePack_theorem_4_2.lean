-- Prove2me | Theorems.Thm_VDCyclePack_theorem_4_2
-- name    : VDCyclePack.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:52.946772+00:00
-- url     : https://prove2.me/theorems/a2ef76d0-2bb6-4ddc-97c5-29c96d005d51
-- title:
--   Theorem 4.2 (Rounding), existence part: a packing $P\subseteq S$ with $|P|\ge\lceil T/(1+16\alpha+16\gamma\log(T+3))\rceil$ (time bound: theorem_4_2_polytime)
-- statement:
--   Let $S$ be a finite family of cycles of a finite graph $G$ with positive weights $(x_C)_{C\in S}$ such that
--   $$
--   \sum_{C\in S,\ v\in V(C)}x_C\le 1\qquad\text{for every } v\in V(G),
--   $$
--   and let $T=\sum_{C\in S}x_C$. Let $\alpha,\gamma\ge0$ be such that every $R\subseteq S$ with $t=|R|$ satisfies
--   $$
--   \beta\Bigl(\bigcup_{C\in R}C\Bigr)\le\alpha t+\gamma t\log_2(t+2).
--   $$
--   Then there is a family $P\subseteq S$ of pairwise vertex-disjoint cycles with
--   $$
--   |P|\ \ge\ \Bigl\lceil\frac{T}{1+16\alpha+16\gamma\log_2(T+3)}\Bigr\rceil .
--   $$
--
--   This is the rounding guarantee applied to the candidate family in the proof of Theorem 1.1. This item is the existence part of Theorem 4.2; the polynomial-time part is the companion item `VDCyclePack.theorem_4_2_polytime`.
--
--   **Formalization Note** $\beta$ is the minimum size of a feedback edge set and logarithms are base two.
--
--   Differences from the source:
--   - generalization: positive rational weights → positive real weights; reason: rational weights are real weights; the statement for rational weights is the special case
--   - encoding: an explicitly given family S of cycles with weights (x_C)_{C∈S} → S : Finset G.Subgraph with WeightedFamily S x (members are cycles, x C > 0, loads ≤ 1), x : G.Subgraph → ℝ read only on S; reason: same instances
--   - encoding: β(⋃_{C∈R} C), log → cycleRank (R.sup id), the minimum size of a feedback edge set of the union in the subgraph lattice; Real.logb 2; reason: the paper's definition of β (p.10), of unions (p.9) and of logarithms (base two, p.9)
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 4.2, p.12

import Mathlib
import Definitions.Def_VDCyclePack_WeightedFamily
import Definitions.Def_VDCyclePack_StructBound
import Definitions.Def_VDCyclePack_IsCyclePacking
import Definitions.Def_VDCyclePack_TR
import Definitions.Def_VDCyclePack_roundingDenom

namespace VDCyclePack

/-- **Theorem 4.2 (rounding), existence of the packing.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 4.2, p.12: "Let S be an explicitly given family of cycles in G with positive
rational weights (x_C)_{C∈S} such that Σ_{C∈S, v∈V(C)} x_C ≤ 1 for every v ∈ V(G), and let
T = Σ_{C∈S} x_C. Let α, γ ≥ 0 be such that every R ⊆ S with t = |R| satisfies
β(⋃_{C∈R} C) ≤ αt + γt log(t + 2). Then one can find in polynomial time a family P ⊆ S of pairwise
vertex-disjoint cycles with |P| ≥ ⌈T / (1 + 16α + 16γ log(T + 3))⌉."

For a family `S` of cycles of a finite graph with positive weights and loads at most one,
`T = Σ_{C∈S} x C`, and `α, γ ≥ 0` satisfying the structural bound, some subfamily `P ⊆ S` is a
cycle packing with `|P| ≥ ⌈T / D⌉`, `D = 1 + 16α + 16γ log₂(T + 3)`.

**Formalization Note.** This item is the existence of `P`; the polynomial-time clause is
`theorem_4_2_polytime`. Weights are real numbers (rational weights are a special case). -/
theorem theorem_4_2 {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset G.Subgraph)
    (x : G.Subgraph → ℝ) (hS : WeightedFamily S x) (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hB : StructBound S α γ) :
    ∃ P ⊆ S, IsCyclePacking P ∧ ⌈TR S x / roundingDenom α γ (TR S x)⌉₊ ≤ P.card := by sorry

end VDCyclePack
