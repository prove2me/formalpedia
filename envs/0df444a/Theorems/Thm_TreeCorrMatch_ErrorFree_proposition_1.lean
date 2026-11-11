-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_proposition_1
-- name    : TreeCorrMatch.ErrorFree.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:26:57.832059+00:00
-- url     : https://prove2.me/theorems/84b7314d-1d4f-4919-b148-c8d3ee561da0
-- title:
--   Proposition 1 — an auxiliary test $\Phi$ with type-I error $\le n^{-\log\log n}$ and power $\ge1-7/\lambda$
-- statement:
--   Let $s\in(\sqrt{C_{\mathrm{Otter}}},1]$ be a constant, $\lambda_n\to\infty$ with $\lambda_n\le(\log n)^K$ for some $K$, and $d=\lceil(\log n)^{1/3}\rceil$. Then for all sufficiently large $n$ there is a test $\Phi:\mathcal Z_d\times\mathcal Z_d\to\{0,1\}$ with
--
--   $$Q\big(\Phi([H_d],[\tilde H_d])=1\big)\le n^{-\log\log n},\qquad P\big(\Phi([H_d],[\tilde H_d])=1\big)\ge1-\frac7\lambda .$$
--
--   The auxiliary test is not computed by the algorithm; it certifies, through the Neyman–Pearson-type bound (22), that the likelihood ratio separates $P$ from $Q$ at an explicit threshold.
--
--   **Formalization Note** A test is given by its acceptance set of pairs of unlabeled trees; it may depend on $n$.
--
--   Differences from the source:
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: 'for all sufficiently large n', with the constants independent of n → ∃ constants, then ∀ᶠ n in atTop; reason: standard reading
--   - encoding: a test Φ : Z_d × Z_d → {0, 1} → its acceptance set Φ ⊆ UTree × UTree, chosen for each large n; reason: a test is determined by the pairs it accepts; only pairs in Z_d × Z_d occur
--   - encoding: Otter's constant C_Otter ≈ 0.338 (cited from [14], not defined in the paper) → otterConst = sup{x ≥ 0 : ∑_m r_m x^m converges}, r_m the number of rooted unlabeled trees with m nodes; reason: the radius of convergence of the generating function of rooted unlabeled trees is Otter's constant 1/α ≈ 0.3383
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 26, Proposition 1 (PDF p. 28)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
import Definitions.Def_TreeCorrMatch_ErrorFree_TBAlign

open Filter Topology

namespace TreeCorrMatch.ErrorFree

theorem proposition_1 (s : ℝ) (hs : Real.sqrt otterConst < s) (hs1 : s ≤ 1) (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop) (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K) :
    ∀ᶠ n : ℕ in atTop, ∃ Φ : Set (UTree × UTree),
      classSetProb (indepPairLaw (lam n) (dParam n)) Φ ≤ (n : ℝ) ^ (-Real.log (Real.log n)) ∧
      1 - 7 / lam n ≤ classSetProb (corrPairLaw (lam n) s (dParam n)) Φ := by sorry

end TreeCorrMatch.ErrorFree
