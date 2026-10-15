-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_trim_to_path
-- name    : SeqLoss.TreeRules.trim_to_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:28.415374+00:00
-- url     : https://prove2.me/theorems/6fa011a0-3f4f-4098-9fd1-1ef4d992ce24
-- title:
--   Proof of Proposition 3, p. 25 — trimming to the path: φ_i(T, ℓ_k) = φ_i(P^k, ℓ_k) for jk ∈ T^i
-- statement:
--   Let $\varphi$ be a rule on loss trees that satisfies tree zero truncation. Let $T$ be a tree, $e=jk\in T$ an edge, $P^k$ the set of edges on the path from the root to $k$, and $i\in N(T)$ an agent with $e\in T^i$ (so $i$ lies on that path). Then
--   $$\varphi_i(T,\ell_e)=\varphi_i(P^k,\ell_e),$$
--   where $\ell_e$ is the loss that is $1$ on $e$ and $0$ elsewhere.
--
--   All edges of $T$ off the path carry zero loss, so the tree can be trimmed to the path without changing the liability of the agents on it.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 25, Appendix A, proof of Proposition 3, third display

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

namespace SeqLoss.TreeRules

theorem trim_to_path (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) (hzt : TreeZeroTruncation φ) (T : Finset (ℕ × ℕ)) (hT : IsTree T)
    (e : ℕ × ℕ) (he : e ∈ T) (i : ℕ) (hi : i ∈ N T) (hon : e ∈ subtreeAt T i) :
    φ T (Pi.single e 1) i = φ (pathTo T e.2) (Pi.single e 1) i := by sorry

end SeqLoss.TreeRules
