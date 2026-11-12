-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_4_1
-- name    : RelatedSchedFPTAS796.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:28.298309+00:00
-- url     : https://prove2.me/theorems/e3e7515f-280f-4e65-b3e8-af97ad0b071c
-- title:
--   Lemma 4.1 ([Bri17]) — a random partition into $k^2$ parts separates any $k$ elements with probability $\ge1/4$
-- statement:
--   Let $X$ be a multiset and $k>0$ an integer, and let $X_1\cup\dots\cup X_{k^2}$ be a random partition of $X$ (every element independently and uniformly into one of the $k^2$ parts). For any $Y\subseteq X$ with $|Y|\le k$, with probability at least $1/4$,
--   $$|Y\cap X_i|\le1\quad\text{for all } i\in\{1,\dots,k^2\}.$$
--
--   This is the colour-coding step of Bringmann's Subset Sum algorithm; repeated $R$ times in Algorithm 1 it separates the jobs that a fixed schedule puts on the machines $1,\dots,d'$.
--
--   Differences from the source:
--   - encoding: a multiset $X$ of integers and $Y\subseteq X$ → the $N$ occurrences of $X$ and a set $Y$ of occurrences; reason: the integer values play no role in the statement
--   - encoding: a random partition of $X$ → a uniformly random map from the occurrences to the parts, probability = fraction of maps; reason: Algorithm 1, lines 2 and 8: each occurrence independently and uniformly into a part
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.10, Lemma 4.1 ([Bri17])

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_RandomPartition

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 4.1 ([Bri17])**, p.10. Let `X` be a multiset (of `N` occurrences) and `k > 0` an
integer. Let `X_1 ∪ ⋯ ∪ X_{k²}` be a random partition of `X`. For any `Y ⊆ X` with `|Y| ≤ k`, with
probability at least `1/4`, `|Y ∩ X_i| ≤ 1` for all `i ∈ {1, …, k²}`. -/
theorem lemma_4_1 (N k : ℕ) (hk : 0 < k) (Y : Finset (Fin N)) (hY : Y.card ≤ k) :
    (1 / 4 : ℝ) ≤ partitionProb N (k ^ 2) (fun f => ∀ i, partCount f Y i ≤ 1) := by sorry

end RelatedSchedFPTAS796.Main
