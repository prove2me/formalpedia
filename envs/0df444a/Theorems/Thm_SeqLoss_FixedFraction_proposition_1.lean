-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_proposition_1
-- name    : SeqLoss.FixedFraction.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:05.583187+00:00
-- url     : https://prove2.me/theorems/21d4a086-5871-4684-bf87-8b840b51a3a7
-- title:
--   Proposition 1, p. 10 — additivity and zero truncation hold iff $\varphi_i(\ell)=\sum_{j\ge i}\ell_j\,\varphi_i(e_j)$
-- statement:
--   A rule $\varphi$ satisfies additivity and zero truncation if and only if, for each $n$, each $\ell\in L^n$ and each agent $i\in\{1,\dots,n\}$,
--   $$\varphi_i(\ell)=\sum_{j\ge i}\ell_j\cdot\varphi_i(e_j),$$
--   where the sum runs over $j=i,\dots,n$ and $e_j=(0,\dots,0,1)\in L^j$ is the elementary $j$-loss problem (agent $i\le j$ is an agent of $e_j$).
--
--   The proposition reduces the choice of an additive, zero-truncating rule to its values on the elementary problems.
--
--   **Formalization Note.** Agents are 0-based. The term $\varphi_i(e_j)$ is `φ (j+1) (elem (j+1)) ⟨i, _⟩` for 0-based $i\le j$; the sum is written over all $j$ with the summand $0$ for $j<i$. Both sides are compared on loss vectors only.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, p. 10, §3.1, Proposition 1; proof Appendix A, p. 22

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

namespace SeqLoss.FixedFraction

theorem proposition_1 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) :
    (Additive φ ∧ ZeroTruncation φ) ↔
    ∀ n (ℓ : Fin n → ℝ), IsLoss ℓ → ∀ i : Fin n,
      φ n ℓ i = ∑ j : Fin n,
        if h : i ≤ j then ℓ j * φ (j.val + 1) (elem (j.val + 1)) ⟨i.val, Nat.lt_succ_of_le h⟩
        else 0 := by sorry

end SeqLoss.FixedFraction
