-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_7
-- name    : TreeCorrMatch.ErrorFree.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:28:12.870941+00:00
-- url     : https://prove2.me/theorems/405c94dc-089e-4639-96cd-4d9e48f6420f
-- title:
--   Lemma 7 — $\mathbb P(A_2^c)=n^{-1+o(1)}$
-- statement:
--   Under the assumptions of Theorem 1, the event $A_2$ that the union graph $\bar G$ has no subgraph $\bar S$ with $|V(\bar S)|<|E(\bar S)|$ and $|V(\bar S)|\le6d+6$, $d=\lceil(\log n)^{1/3}\rceil$, satisfies
--
--   $$\mathbb P(A_2^c)=n^{-1+o(1)},$$
--
--   that is, there is a sequence $f_n\to0$ with $\mathbb P(A_2^c)=n^{-1+f_n}$ for all large $n$.
--
--   Small subgraphs with more edges than nodes (two cycles) are what a wrong match passing the 5-dangling-tree test would create; this lemma excludes them everywhere in the union graph.
--
--   Differences from the source:
--   - reading: P(A_2^c) = n^{-1+o(1)} → ∃ f → 0, for all large n: P(A_2^c) = n^{-1+f(n)} (two-sided); reason: the literal meaning of the notation; the stronger of the two readings (the upper bound alone is the other); see INSIGHTS.yaml I1
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: CER(n, λ, s) with parent edge probability λ/(ns), λ ∈ (0, ns] → parent edge probability clamped to [0, 1]; reason: the clamp changes only the finitely many n with λ_n > ns and no limit
--   - encoding: Otter's constant C_Otter ≈ 0.338 (cited from [14], not defined in the paper) → otterConst = sup{x ≥ 0 : ∑_m r_m x^m converges}, r_m the number of rooted unlabeled trees with m nodes; reason: the radius of convergence of the generating function of rooted unlabeled trees is Otter's constant 1/α ≈ 0.3383
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 20, Lemma 7 (PDF p. 22)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_AnalysisEvents

open Filter Topology

namespace TreeCorrMatch.ErrorFree

theorem lemma_7 (s : ℝ) (hs : Real.sqrt otterConst < s) (hs1 : s ≤ 1) (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop) (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K) :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      cerProb n (lam n) s (fun x => ¬ EventA2 x) = (n : ℝ) ^ (-1 + f n) := by sorry

end TreeCorrMatch.ErrorFree
