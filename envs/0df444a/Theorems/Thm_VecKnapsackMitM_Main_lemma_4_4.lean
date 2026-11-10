-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_lemma_4_4
-- name    : VecKnapsackMitM.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:35:31.864591+00:00
-- url     : https://prove2.me/theorems/f1a3eac5-0fa0-43f8-a13b-d86fa11f8f38
-- title:
--   Lemma 4.4 — embed(S₁) ∈ range(S₂) iff S₁, S₂ can be matched
-- statement:
--   For every $d$-Knapsack instance $(I,\bar W)$ ($d\ge2$, nonnegative data) and all sets of items $S_1,S_2\subseteq I$: $\mathrm{embed}(S_1)\in\mathrm{range}_{\bar W}(S_2)$ if and only if $S_1$ and $S_2$ can be matched, i.e. $\bar w(S_1)+\bar w(S_2)\le\bar W$ and $\max(S_1)<\min(S_2)$ (with $\max(\emptyset)=-\infty$, $\min(\emptyset)=\infty$).
--
--   Differences from the source:
--   - encoding: items I = {1, …, n} and dimensions t ∈ {1, …, d} → items Fin n (the paper's item i+1 is i) and dimensions Fin d (the paper's dimension t+1 is t: w̄_1 is t = 0, w̄_d is t = d − 1, the middle dimensions 2, …, d − 1 are 1 ≤ t, t + 2 ≤ d); reason: zero-based finite indexing; same instances and same sets
--   - encoding: points and boxes in (ℝ ∪ {±∞})^{d+1}, max(S), min(S) of 1-based indices → EReal coordinates; maxIdx, minIdx of 0-based indices (both shifted by −1); b_{d+1} = minIdx S − 1 with ⊤ − 1 = ⊤; reason: a uniform shift changes neither max(S₁) < min(S₂) nor max(S₁) ≤ min(S₂) − 1; EReal realizes the conventions max(∅) = −∞, min(∅) = ∞, ∞ − 1 = ∞
--   - generalization: §2 assumes profit order and individually feasible items throughout the paper → arbitrary item order and no individual-feasibility assumption; reason: the slack lemma uses only nonnegative item data; geometric matching uses only nonnegative weights and the fixed indices; both specialize to every source instance
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Lemma 4.4 and Definition 4.3, printed p. 18 (PDF 19)

import Mathlib
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Geometry

namespace VecKnapsackMitM.Main

/-- Bringmann, Kulik, Węgrzycki (2026), Lemma 4.4, printed p. 18 (PDF 19). For any sets of
items `S₁, S₂`, `embed(S₁) ∈ range_W̄(S₂)` if and only if `S₁` and `S₂` can be matched
(`w̄(S₁) + w̄(S₂) ≤ W̄` and `max(S₁) < min(S₂)`). -/
theorem lemma_4_4 (d n : ℕ) (hd : 2 ≤ d) (inst : Instance d n) (hinst : inst.Nonneg)
    (S₁ S₂ : Finset (Fin n)) :
    InBox (rangeLo d) (rangeHi inst S₂) (embed inst.toItems S₁) ↔ Matched inst S₁ S₂ := by sorry

end VecKnapsackMitM.Main
