-- Prove2me | Theorems.Thm_SymBoolPCSP_LPRounding_case1_claim
-- name    : SymBoolPCSP.LPRounding.case1_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:24.042558+00:00
-- url     : https://prove2.me/theorems/05a3e96f-bcab-4b59-b66d-7332e8b363cf
-- title:
--   §3.2, proof, Case 1, p. 14 — some probability vector $v$ has $(Mv)_i \ne 1/2$ for all $i$
-- statement:
--   Let $n \ge 1$ and let $M \in ([0,1] \cap \mathbb Q)^{n \times n}$ be a rational matrix whose diagonal entries satisfy $M_{i,i} \in \{0,1\}$ for every $i$. Then there is a rational vector $v \in [0,1]^n$ with $\sum_j v_j = 1$ such that
--   $$(Mv)_i = \sum_{j=1}^n M_{i,j} v_j \ne \tfrac12 \qquad \text{for all } i \in [n].$$
--
--   In the Majority case of the correctness proof, $M$ is the matrix whose $i$-th column is an LP solution with $i$-th coordinate in $\{0,1\}$, and $Mv$ is then an LP solution with no coordinate equal to $1/2$, ready to be rounded.
--
--   **Formalization Note** The paper first finds a real $v$ and then perturbs it to a rational one; this item states the combined claim directly over $\mathbb Q$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 14, §3.2, proof, Case 1 (claim and the perturbation to rational v′)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.LPRounding

/-- §3.2, proof, Case 1, p. 14: for an `n × n` rational matrix `M` with entries in `[0, 1]` and
every diagonal entry in `{0, 1}` (`n ≥ 1`), there is a rational `v ∈ [0, 1]^n` with coordinate
sum `1` such that `(Mv)_i ≠ 1/2` for all `i`. -/
theorem case1_claim (n : ℕ) (hn : 0 < n) (M : Fin n → Fin n → ℚ)
    (hM : ∀ i j, 0 ≤ M i j ∧ M i j ≤ 1) (hdiag : ∀ i, M i i = 0 ∨ M i i = 1) :
    ∃ v : Fin n → ℚ, (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧ ∑ j, v j = 1 ∧
      ∀ i, ∑ j, M i j * v j ≠ 1 / 2 := by sorry

end SymBoolPCSP.LPRounding
