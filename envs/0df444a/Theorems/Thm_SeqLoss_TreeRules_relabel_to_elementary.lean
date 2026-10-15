-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_relabel_to_elementary
-- name    : SeqLoss.TreeRules.relabel_to_elementary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:43.846774+00:00
-- url     : https://prove2.me/theorems/fdeaeed5-0c8e-4ad8-8d8c-cccfd3f42bbe
-- title:
--   Proof of Proposition 3, p. 25 — relabelling P^k: φ_i(P^k, ℓ_k) = φ_[i](e_[j]) (page: e_[k])
-- statement:
--   Let $\varphi$ be a rule on loss trees (in particular, invariant to agent labels). Let $T$ be a tree, $e=jk\in T$ an edge, $P^k$ the path from the root to $k$, and $[v]$ the number of vertices on the path from the root to $v$. Then for each agent $i\in N(P^k)$,
--   $$\varphi_i(P^k,\ell_e)=\varphi_{[i]}\big(e_{[j]}\big),$$
--   where $\ell_e$ is the loss that is $1$ on $e$ and $0$ elsewhere and $e_n=(T_n,\ell_n)$ is the elementary tree problem.
--
--   Relabelling the vertices of $P^k$ by their position on the path turns $(P^k,\ell_e)$ into the elementary problem $e_{[j]}$, and label invariance transfers the liabilities.
--
--   **Formalization Note** The page writes $e_{[k]}$. The path $P^k$ has $[k]$ vertices and $[k]-1=[j]$ edges, and $e_n$ has $n$ edges, so the relabelled problem is $e_{[j]}$; for instance in Figure 2 the loss $\ell(24)$ is shared by agents 1 and 2 as in $e_2$, while $[4]=3$. The corrected index is stated.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 25, Appendix A, proof of Proposition 3, last display (index corrected from e_[k] to e_[j])

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting

namespace SeqLoss.TreeRules

theorem relabel_to_elementary (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) (T : Finset (ℕ × ℕ)) (hT : IsTree T) (e : ℕ × ℕ) (he : e ∈ T) :
    ∀ i ∈ N (pathTo T e.2), φ (pathTo T e.2) (Pi.single e 1) i =
      φ (treeChain (depth T e.1)) (chainLoss (depth T e.1)) (depth T i) := by sorry

end SeqLoss.TreeRules
