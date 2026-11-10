-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_lemma_3_1
-- name    : VecKnapsackMitM.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:33:30.165135+00:00
-- url     : https://prove2.me/theorems/d38efcd2-d892-4558-923b-d8554c5550a1
-- title:
--   Lemma 3.1 — Slack-Generating Lemma
-- statement:
--   Let $d\ge2$, let $(I,\bar W)$ be a $d$-Knapsack instance (nonnegative profits, weights and capacities), let $S\subseteq I$ be nonempty and $0<\delta<1$. Then there is $Q\subseteq S$ with
--   1. $\bar w_t(Q)\le(1-\delta)\,\bar w_t(S)$ for every $t\in\{1,\dots,d-1\}$;
--   2. $p(Q)\ge(1-\delta)\,p(S)-(d-1)\max_{i\in S}p(i)$;
--   3. $\max\{p(Q),\max_{i\in S}p(i)\}\ge\frac{1-\delta}{d}\,p(S)$.
--
--   Differences from the source:
--   - encoding: items I = {1, …, n} and dimensions t ∈ {1, …, d} → items Fin n (the paper's item i+1 is i) and dimensions Fin d (the paper's dimension t+1 is t: w̄_1 is t = 0, w̄_d is t = d − 1, the middle dimensions 2, …, d − 1 are 1 ≤ t, t + 2 ≤ d); reason: zero-based finite indexing; same instances and same sets
--   - generalization: §2 assumes profit order and individually feasible items throughout the paper → arbitrary item order and no individual-feasibility assumption; reason: the slack lemma uses only nonnegative item data; geometric matching uses only nonnegative weights and the fixed indices; both specialize to every source instance
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Lemma 3.1, printed p. 8 (PDF 9)

import Mathlib
import Definitions.Def_VecKnapsackMitM_Main_Instance

namespace VecKnapsackMitM.Main

/-- Bringmann, Kulik, Węgrzycki (2026), Lemma 3.1 (Slack-Generating Lemma), printed p. 8
(PDF 9). For a d-Knapsack instance, a nonempty `S` and `0 < δ < 1` there is `Q ⊆ S` with
(1) `w̄_t(Q) ≤ (1 − δ) w̄_t(S)` for the paper's `t ∈ {1, …, d − 1}` (here `t + 1 < d`),
(2) `p(Q) ≥ (1 − δ) p(S) − (d − 1) max_{i ∈ S} p(i)`, and
(3) `max{p(Q), max_{i ∈ S} p(i)} ≥ (1 − δ)/d · p(S)`. -/
theorem lemma_3_1 (d n : ℕ) (hd : 2 ≤ d) (inst : Instance d n) (hinst : inst.Nonneg)
    (S : Finset (Fin n)) (hS : S.Nonempty) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ Q ⊆ S,
      (∀ t : Fin d, t.val + 1 < d →
        inst.toItems.weight Q t ≤ (1 - δ) * inst.toItems.weight S t) ∧
      (1 - δ) * inst.toItems.profit S - ((d : ℝ) - 1) * S.sup' hS inst.p ≤
        inst.toItems.profit Q ∧
      (1 - δ) / d * inst.toItems.profit S ≤ max (inst.toItems.profit Q) (S.sup' hS inst.p) := by sorry

end VecKnapsackMitM.Main
