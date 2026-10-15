-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_off_path_not_liable
-- name    : SeqLoss.TreeRules.off_path_not_liable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:24.562334+00:00
-- url     : https://prove2.me/theorems/e83decdc-78b8-4644-b72d-4205eb8a6507
-- title:
--   Proof of Proposition 3, p. 25 — an agent i with jk ∉ T^i is not liable for the unit loss on jk
-- statement:
--   Let $\varphi$ be a rule on loss trees that satisfies tree zero truncation. Let $T$ be a tree, $e=jk\in T$ an edge, and $i\in N(T)$ an agent such that $e\notin T^i$, i.e. $i$ is neither $j$ nor an ancestor of $j$. Then
--   $$\varphi_i(T,\ell_e)=0,$$
--   where $\ell_e$ is the loss that is $1$ on $e$ and $0$ elsewhere.
--
--   This is the claim that "agents not on the path $P^k$ will not be liable for the non-zero loss"; it is the zero under the brace in the second display of the proof of Proposition 3, and it restricts each agent's liability to the losses in its own subtree $T^i$.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 25, Appendix A, proof of Proposition 3, second display

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

namespace SeqLoss.TreeRules

theorem off_path_not_liable (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) (hzt : TreeZeroTruncation φ) (T : Finset (ℕ × ℕ)) (hT : IsTree T)
    (e : ℕ × ℕ) (he : e ∈ T) (i : ℕ) (hi : i ∈ N T) (hoff : e ∉ subtreeAt T i) :
    φ T (Pi.single e 1) i = 0 := by sorry

end SeqLoss.TreeRules
