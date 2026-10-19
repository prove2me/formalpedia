-- Prove2me | Theorems.Thm_ProcFlex_DMGI_proposition_3
-- name    : ProcFlex.DMGI.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:24.629994+00:00
-- url     : https://prove2.me/theorems/313da505-9be7-4367-b4a0-04d443da7e50
-- title:
--   Proposition 3: worst-case profit as a DMGI minimum
-- statement:
--   Let $U$ be a nonempty compact set of nonnegative demands whose residuals $E=\{d-\mu:d\in U\}$ are part-wise independently symmetric. For a flexibility design $A$, worst-case profit is the attained minimum
--
--   $$
--   R^g(A,U)=\min_{K\in Q,\,\epsilon\in E}\left(\delta^K_\mu(A)+\sum_t\sum_{r<t}\beta_{tr}\sum_{i=H_{tr}-k_{tr}+1}^{H_{tr}}\epsilon_{s_t,i}\right).
--   $$
--
--   Here $K$ fixes the counts of product dual levels, $H_{tr}$ is their cumulative count, and the residuals in each category are listed in increasing product-index order. This is the profit-only representation underlying Theorem 1.
--
--   **Formalization Note** Nonempty compact $U$ makes the printed minimum an attained one. The DMGI includes the omitted condition $z\ge0$ from (4).
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 41, Proposition 3 and (7)

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

namespace ProcFlex.DMGI

/-- Proposition 3 and equation (7), p. 41: the attained DMGI representation
of worst-case profit. -/
theorem proposition_3 {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A : Design m n) (U : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (hU : IsSymmetricAround S U μ)
    (hUpos : ∀ d ∈ U, ∀ i, 0 ≤ d i)
    (hUne : U.Nonempty) (hUc : IsCompact U) :
    IsLeast {v : ℝ | ∃ (K : Fin T → Fin (T + 1) → ℕ), InQ S K ∧
      ∃ ε ∈ ((fun d => d - μ) '' U),
        v = dmgi S μ K A + blockSum S K ε}
      (Rf S (fun x _ => x) A U) := by sorry

end ProcFlex.DMGI
