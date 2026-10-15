-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_proposition_3
-- name    : SeqLoss.TreeRules.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:29.342291+00:00
-- url     : https://prove2.me/theorems/06f6d32a-3266-4247-8713-6946dea4a485
-- title:
--   Proposition 3, p. 25 — tree additivity and zero truncation iff φ_i(T, ℓ) = Σ_{jk∈T^i} ℓ(jk) φ_[i](e_[j])
-- statement:
--   Let $\varphi$ be a rule on loss trees. Then $\varphi$ satisfies tree additivity and tree zero truncation if and only if, for every tree $T$, every loss $\ell\ge 0$ and every agent $i\in N(T)$,
--   $$\varphi_i(T,\ell)=\sum_{jk\in T^i}\ell(jk)\,\varphi_{[i]}\big(e_{[j]}\big).$$
--   Here $T^i$ is the subtree of $T$ rooted at $i$, $[v]$ is the number of vertices on the path from the root to $v$, and $e_n=(T_n,\ell_n)$ is the elementary tree problem.
--
--   Proposition 3 is the tree analogue of Proposition 1: every problem decomposes into elementary problems, so a rule satisfying the two axioms is determined by its values on $e_1,e_2,\dots$. Together with Proposition 2 it yields Theorem 4.
--
--   **Formalization Note** The page writes $\varphi_{[i]}(e_{[k]})$. With $e_{[k]}$ the statement is false for the fixed-fraction rules (in Figure 2, agent 2's share of $\ell(24)$ would be $\varphi^\lambda_2(e_3)=0$ instead of $\lambda$); the correct index is $[j]=[k]-1$, which is what the proof's relabelling produces.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 25, Proposition 3 (index corrected from e_[k] to e_[j])

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

namespace SeqLoss.TreeRules

theorem proposition_3 (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) :
    (TreeAdditive φ ∧ TreeZeroTruncation φ) ↔
      ∀ T, IsTree T → ∀ ℓ, IsTreeLoss ℓ → ∀ i ∈ N T,
        φ T ℓ i = ∑ e ∈ subtreeAt T i,
          ℓ e * φ (treeChain (depth T e.1)) (chainLoss (depth T e.1)) (depth T i) := by sorry

end SeqLoss.TreeRules
