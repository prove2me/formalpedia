-- Prove2me | Theorems.Thm_SqrtAgreement_SRA_perm_payoff_equivalence
-- name    : SqrtAgreement.SRA.perm_payoff_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:43.384495+00:00
-- url     : https://prove2.me/theorems/05624811-9040-4de1-a611-5c69c924792c
-- title:
--   §5, p. 25 — symmetric fully informative profiles inherit (strict) equilibrium from truthful behavior and are payoff-equivalent to it
-- statement:
--   In the SRA game, let $\sigma$ be a permutation of the answer set $\mathcal Y$, and consider the symmetric fully informative profile in which every agent reports $\sigma(y)$ whenever she observes $y$. Then:
--
--   1. if the truthful profile is a Bayes–Nash equilibrium, so is the $\sigma$-profile;
--   2. if the truthful profile is a strict Bayes–Nash equilibrium, so is the $\sigma$-profile;
--   3. for every agent $j$, the expected payment under the $\sigma$-profile equals the expected payment under the truthful profile:
--   $$\mathbb E_{\sigma}[\tau_j]=\mathbb E_{\mathbf t}[\tau_j].$$
--
--   The statement holds for every number of tasks and every generating model, since SRA treats answers symmetrically. It lets results proved for truthful reporting transfer to every fully informative symmetric profile.
--
--   **Formalization Note** The page says "if truthful behavior is an equilibrium, then so is any symmetric fully informative strategy profile … And all such equilibria are payoff-equivalent." Item 2 is the same relabeling argument for strict equilibria; Theorem 2(1) needs it. No validity hypotheses are needed.
-- source:
--   Kamble, Shah, Marn, Parekh & Ramchandran, The Square Root Agreement Rule for Incentivizing Truthful Feedback on Online Platforms, arXiv:1507.07045v5, p. 25, §5 (first paragraph)

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

namespace SqrtAgreement.SRA

theorem perm_payoff_equivalence {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M)
    (σ : Equiv.Perm (Fin k)) :
    (IsBNE G K S (symm (truthful k)) → IsBNE G K S (symm (permStrat σ))) ∧
    (IsStrictBNE G K S (symm (truthful k)) → IsStrictBNE G K S (symm (permStrat σ))) ∧
    ∀ j : Fin M,
      expPay G K S (symm (permStrat σ)) j = expPay G K S (symm (truthful k)) j := by sorry

end SqrtAgreement.SRA
