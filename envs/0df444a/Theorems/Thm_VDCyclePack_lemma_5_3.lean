-- Prove2me | Theorems.Thm_VDCyclePack_lemma_5_3
-- name    : VDCyclePack.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:45.306088+00:00
-- url     : https://prove2.me/theorems/327860a5-5148-4a32-a9fc-a905e3ba457e
-- title:
--   Lemma 5.3: every nonempty $R\subseteq S$ contains a cycle $C$ with $m_R(C)\le D$
-- statement:
--   Let $S$, $x$, $T=\sum_{C\in S}x_C$, $\alpha,\gamma\ge0$ be as in Theorem 4.2 and put $D=1+16\alpha+16\gamma\log_2(T+3)$. Every nonempty $R\subseteq S$ contains a cycle $C$ with
--   $$
--   m_R(C)=\sum_{C'\in R,\ V(C')\cap V(C)\neq\emptyset}x_{C'}\ \le\ D .
--   $$
--
--   The bound uses the initial total weight $T$, so the same $D$ applies at every step of the greedy rounding; this gives Theorem 4.2.
--
--   **Formalization Note** The hypotheses are those of `theorem_4_2`.
--
--   Differences from the source:
--   - generalization: positive rational weights → positive real weights; reason: rational weights are real weights; the statement for rational weights is the special case
--   - encoding: an explicitly given family S of cycles with weights (x_C)_{C∈S} → S : Finset G.Subgraph with WeightedFamily S x (members are cycles, x C > 0, loads ≤ 1), x : G.Subgraph → ℝ read only on S; reason: same instances
--   - encoding: β(⋃_{C∈R} C), log → cycleRank (R.sup id), the minimum size of a feedback edge set of the union in the subgraph lattice; Real.logb 2; reason: the paper's definition of β (p.10), of unions (p.9) and of logarithms (base two, p.9)
--   - encoding: D = 1 + 16α + 16γ log(T + 3) with the initial T; m_R(C) → roundingDenom α γ (TR S x); mR R x C; reason: the paper's definitions (p.14)
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 5.3, p.17 (with D from Section 5, p.14)

import Mathlib
import Definitions.Def_VDCyclePack_WeightedFamily
import Definitions.Def_VDCyclePack_StructBound
import Definitions.Def_VDCyclePack_mR
import Definitions.Def_VDCyclePack_TR
import Definitions.Def_VDCyclePack_roundingDenom

namespace VDCyclePack

/-- **Lemma 5.3 (a cheap cycle exists).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 5.3, p.17: "Every nonempty R ⊆ S contains a cycle C with m_R(C) ≤ D." Here
(Section 5, p.14) "Fix S, x, T, α, and γ as in the theorem, and put D = 1 + 16α + 16γ log(T + 3)";
p.17: "The bound uses the initial total weight T".

Under the hypotheses of Theorem 4.2 (`S` a family of cycles with positive weights and loads at most
one, `α, γ ≥ 0` with the structural bound for every subfamily of `S`), every nonempty `R ⊆ S`
contains a cycle `C` with `m_R(C) ≤ D`, where `D = 1 + 16α + 16γ log₂(T + 3)` and `T = Σ_{C∈S} x C`.

**Formalization Note.** `D` is computed from the initial total weight `T = TR S x`, not from `T_R`.
The weighted-average inequality (2), p.15, is a step of the proof. -/
theorem lemma_5_3 {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset G.Subgraph)
    (x : G.Subgraph → ℝ) (hS : WeightedFamily S x) (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hB : StructBound S α γ) :
    ∀ R ⊆ S, R.Nonempty → ∃ C ∈ R, mR R x C ≤ roundingDenom α γ (TR S x) := by sorry

end VDCyclePack
