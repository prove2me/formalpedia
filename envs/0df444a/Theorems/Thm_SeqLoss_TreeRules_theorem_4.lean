-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_theorem_4
-- name    : SeqLoss.TreeRules.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:37.207678+00:00
-- url     : https://prove2.me/theorems/a1f633b7-5e54-483f-8d34-16d094d57209
-- title:
--   Theorem 4 — on loss trees, tree additivity, tree zero truncation, merging proofness and population monotonicity characterize the fixed-fraction rules
-- statement:
--   Let $\varphi$ be a rule on loss trees: for every tree $T$ and loss $\ell\ge 0$ it assigns non-negative liabilities $\varphi_i(T,\ell)$ to the non-leaf agents $i\in N(T)$ that sum to the total loss, it is invariant to agent labels, and it is continuous along $a\ell\to\ell$. Then $\varphi$ satisfies
--
--   1. tree additivity (Axiom 5),
--   2. tree zero truncation (Axiom 6),
--   3. merging proofness (Axiom 4, on $e_2,e_3$), and
--   4. population monotonicity (Axiom 3, on $e_n$),
--
--   if and only if there is $\lambda\in[0,1]$ such that, for every tree $T$, loss $\ell$ and agent $i\in N(T)$,
--   $$\varphi_i(T,\ell)=\varphi^\lambda_i(T,\ell)=\lambda\sum_{ij\in T}\ell(ij)+[i \text{ is the root}]\,(1-\lambda)\sum_{e\in T}\ell(e).$$
--
--   Theorem 4 extends the characterization of the fixed-fraction rules (Theorem 1) from loss chains to loss trees, in which one agent may cause losses to several others.
--
--   **Formalization Note** The equality $\varphi=\varphi^\lambda$ is stated at every tree, non-negative loss and agent of $N(T)$, the only arguments at which a rule carries meaning. Axiom 6 is read as adding a zero-loss edge to a new leaf (the sentence before the axiom), and Axiom 3 uses the range $1\le j<n$; see the Axioms file.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 17, Theorem 4 (restated p. 24)

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

namespace SeqLoss.TreeRules

theorem theorem_4 (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) (hφ : IsTreeRule φ) :
    (TreeAdditive φ ∧ TreeZeroTruncation φ ∧ TreeMergingProof φ ∧ TreePopulationMonotone φ) ↔
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∀ T, IsTree T → ∀ ℓ, IsTreeLoss ℓ → ∀ i ∈ N T,
        φ T ℓ i = fixedFractionTree lam T ℓ i := by sorry

end SeqLoss.TreeRules
