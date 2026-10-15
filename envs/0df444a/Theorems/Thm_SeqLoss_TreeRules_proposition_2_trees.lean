-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_proposition_2_trees
-- name    : SeqLoss.TreeRules.proposition_2_trees
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:37.616462+00:00
-- url     : https://prove2.me/theorems/9b24e342-681e-4355-8bd7-3f13e413b3f7
-- title:
--   Proposition 2 (p. 12) on the tree problems e_n ≡ (T_n, ℓ_n) (p. 17) — PM and MP iff φ(e_n) = φ^λ(e_n)
-- statement:
--   Let $\varphi$ be a rule on loss trees and let $e_n=(T_n,\ell_n)$ with $T_n=\{12,23,\dots,(n,n+1)\}$ and $\ell_n$ the unit loss on $(n,n+1)$. Then $\varphi$ satisfies population monotonicity and merging proofness if and only if there is $\lambda\in[0,1]$ such that, for each $n\ge 1$,
--   $$\varphi_i(e_n)=\varphi^\lambda_i(e_n)\qquad\text{for } i=1,\dots,n.$$
--   Concretely $\varphi^\lambda(e_1)=(1)$ and, for $n\ge 2$, $\varphi^\lambda(e_n)=(1-\lambda,0,\dots,0,\lambda)$.
--
--   The paper proves Proposition 2 for the linear model and states (p. 17) that population monotonicity and merging proofness "extend immediately to the new setting"; this is that extension, the elementary-problem half of Theorem 4.
--
--   **Formalization Note** Population monotonicity uses the range $1\le j<n$ (the page prints $1<j<n$, under which the linear Proposition 2 is false).
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 12, Proposition 2, applied to e_n ≡ (T_n, ℓ_n) as stated on p. 17

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

namespace SeqLoss.TreeRules

theorem proposition_2_trees (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) :
    (TreePopulationMonotone φ ∧ TreeMergingProof φ) ↔
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, 1 ≤ n → ∀ i ∈ Finset.Icc 1 n,
        φ (treeChain n) (chainLoss n) i = fixedFractionTree lam (treeChain n) (chainLoss n) i := by sorry

end SeqLoss.TreeRules
