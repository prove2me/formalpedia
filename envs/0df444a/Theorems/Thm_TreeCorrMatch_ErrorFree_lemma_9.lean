-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_9
-- name    : TreeCorrMatch.ErrorFree.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:26:54.008197+00:00
-- url     : https://prove2.me/theorems/960c4f5c-6de1-4beb-85e4-753d5509185d
-- title:
--   Lemma 9 — a set $\mathcal F_{d-l}$ with $Q$-probability $\le C_3e^{-d+l}$ and $P$-probability $\ge1-C_4\lambda^{-1}$
-- statement:
--   Let $s\in(\sqrt{C_{\mathrm{Otter}}},1]$ be a constant, let $\lambda_n\to\infty$ with $\lambda_n\le(\log n)^K$ for some $K$, and set $d=\lceil(\log n)^{1/3}\rceil$ and $l=\lceil2\log\log n\rceil$. Then there are constants $C_3,C_4>0$ such that for all large $n$ there is a set $\mathcal F_{d-l}\subseteq\mathcal Z_{d-l}\times\mathcal Z_{d-l}$ with
--
--   $$Q\big(([H_{d-l}],[\tilde H_{d-l}])\in\mathcal F_{d-l}\big)\le C_3e^{-d+l},\qquad P\big(([H_{d-l}],[\tilde H_{d-l}])\in\mathcal F_{d-l}\big)\ge1-C_4\lambda^{-1}.$$
--
--   This is the tree-correlation result of [10, Appendix A–C], carried over to $\lambda=(\log n)^{O(1)}$; it is where the threshold $s>\sqrt{C_{\mathrm{Otter}}}$ enters.
--
--   Differences from the source:
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: 'for all sufficiently large n', with the constants independent of n → ∃ constants, then ∀ᶠ n in atTop; reason: standard reading
--   - encoding: d − l, a nonnegative integer for large n → natural-number subtraction dParam n − ⌈2 log log n⌉₊; reason: d > l for all large n, where the statement is made
--   - encoding: Otter's constant C_Otter ≈ 0.338 (cited from [14], not defined in the paper) → otterConst = sup{x ≥ 0 : ∑_m r_m x^m converges}, r_m the number of rooted unlabeled trees with m nodes; reason: the radius of convergence of the generating function of rooted unlabeled trees is Otter's constant 1/α ≈ 0.3383
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 27, Lemma 9 (PDF p. 29)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
import Definitions.Def_TreeCorrMatch_ErrorFree_TBAlign

open Filter Topology

namespace TreeCorrMatch.ErrorFree

theorem lemma_9 (s : ℝ) (hs : Real.sqrt otterConst < s) (hs1 : s ≤ 1) (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop) (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K) :
    ∃ C3 C4 : ℝ, 0 < C3 ∧ 0 < C4 ∧ ∀ᶠ n : ℕ in atTop,
      ∃ F : Set (UTree × UTree),
        F ⊆ Zk (dParam n - ⌈2 * Real.log (Real.log n)⌉₊) ×ˢ
            Zk (dParam n - ⌈2 * Real.log (Real.log n)⌉₊) ∧
        classSetProb (indepPairLaw (lam n) (dParam n - ⌈2 * Real.log (Real.log n)⌉₊)) F ≤
          C3 * Real.exp (-(dParam n : ℝ) + (⌈2 * Real.log (Real.log n)⌉₊ : ℝ)) ∧
        1 - C4 * (lam n)⁻¹ ≤
          classSetProb (corrPairLaw (lam n) s (dParam n - ⌈2 * Real.log (Real.log n)⌉₊)) F := by sorry

end TreeCorrMatch.ErrorFree
