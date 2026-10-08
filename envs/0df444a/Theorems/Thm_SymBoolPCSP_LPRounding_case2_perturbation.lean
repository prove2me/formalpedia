-- Prove2me | Theorems.Thm_SymBoolPCSP_LPRounding_case2_perturbation
-- name    : SymBoolPCSP.LPRounding.case2_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:12.27087+00:00
-- url     : https://prove2.me/theorems/860571b6-35b7-4f38-9baa-69000b3d8d79
-- title:
--   §3.2, proof, Case 2, pp. 14–15 — some probability vector $v$ has $(Mv)_i \ne \hat w_i$ wherever $\hat w_i \notin \{0,1\}$
-- statement:
--   Let $n \ge 1$, let $M \in ([0,1] \cap \mathbb Q)^{n \times n}$ be a rational matrix with $M_{i,i} \in \{0,1\}$ for every $i$, and let $\hat w \in \mathbb Q^n$ be any rational vector. Then there is a rational vector $v \in [0,1]^n$ with $\sum_j v_j = 1$ such that $w = Mv$ satisfies
--   $$w_i \ne \hat w_i \qquad \text{for every } i \in [n] \text{ with } \hat w_i \notin \{0,1\}.$$
--
--   In the Alternating-Threshold case of the correctness proof, $\hat w$ is a rational LP solution and $w = Mv$ is a second LP solution that differs from $\hat w$ at every coordinate where $\hat w$ is fractional.
--
--   **Formalization Note** The paper takes $\hat w$ to be a rational LP solution; the statement here holds for every rational vector $\hat w$, which includes that case. The claim is stated directly over $\mathbb Q$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, pp. 14–15, §3.2, proof, Case 2 (choice of v, w)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.LPRounding

/-- §3.2, proof, Case 2, pp. 14–15: for an `n × n` rational matrix `M` with entries in `[0, 1]`
and every diagonal entry in `{0, 1}` (`n ≥ 1`), and any rational vector `ŵ`, there is a rational
`v ∈ [0, 1]^n` with coordinate sum `1` such that `w = Mv` has `w_i ≠ ŵ_i` for every `i` with
`ŵ_i ∉ {0, 1}`. -/
theorem case2_perturbation (n : ℕ) (hn : 0 < n) (M : Fin n → Fin n → ℚ)
    (hM : ∀ i j, 0 ≤ M i j ∧ M i j ≤ 1) (hdiag : ∀ i, M i i = 0 ∨ M i i = 1)
    (what : Fin n → ℚ) :
    ∃ v : Fin n → ℚ, (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧ ∑ j, v j = 1 ∧
      ∀ i, what i ≠ 0 → what i ≠ 1 → ∑ j, M i j * v j ≠ what i := by sorry

end SymBoolPCSP.LPRounding
