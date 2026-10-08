-- Prove2me | Theorems.Thm_TensorNP_Rank_eq29_iff_system30
-- name    : TensorNP.Rank.eq29_iff_system30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:03.93099+00:00
-- url     : https://prove2.me/theorems/e34d6ade-1c62-4c97-a63c-3bce29e57dda
-- title:
--   Proof of Theorem 1.14, (29) — rank ≤ 2 gives two outer products, and (29) for A is the system (30)
-- statement:
--   This item makes precise the step "Suppose not and that there exist $\mathbf u_i, \mathbf v_i \in \mathbb Q^2$ with (29). Identity (29) gives eight equations found in (30)" of the proof of Theorem 1.14. It has two parts.
--
--   1. Let $E$ be a field and $\mathcal B \in E^{l\times m\times n}$. If $\operatorname{rank}_E(\mathcal B) \le 2$, then there are $\mathbf u_1,\mathbf v_1 \in E^l$, $\mathbf u_2,\mathbf v_2\in E^m$, $\mathbf u_3,\mathbf v_3 \in E^n$ with $\mathcal B = \mathbf u_1\otimes\mathbf u_2\otimes\mathbf u_3 + \mathbf v_1\otimes\mathbf v_2\otimes\mathbf v_3$.
--   2. Let $K$ be a field of characteristic zero, $\mathcal A$ the rational tensor of Theorem 1.14 with entries read in $K$, and $\mathbf u_i = [a_i,b_i]^\top$, $\mathbf v_i = [c_i,d_i]^\top \in K^2$ for $i = 1,2,3$. Then
--   $$
--   \mathcal A = \mathbf u_1\otimes\mathbf u_2\otimes\mathbf u_3 + \mathbf v_1\otimes\mathbf v_2\otimes\mathbf v_3 \tag{29}
--   $$
--   holds if and only if $a_1,\dots,d_3$ satisfy the eight equations (30).
--
--   Applied with $E = K = \mathbb Q$, the two parts turn "$\operatorname{rank}_{\mathbb Q}(\mathcal A) \le 2$" into a rational solution of (30).
--
--   **Formalization Note** The paper only says "suppose not"; part 1 is the step that absorbs the scalars $\lambda_s$ and pads a decomposition with fewer than two terms by zero terms. It is stated for an arbitrary tensor over an arbitrary field so that it is not vacuous (for the paper's $\mathcal A$ over $\mathbb Q$ its hypothesis is false, by Lemma 8.1). Part 2 is stated over every field of characteristic zero for the same reason; over $\mathbb R$ both sides hold for the decomposition of the first milestone. The paper says (29) "gives" (30); the equivalence states that (30) is exactly the entrywise reading of (29). Vectors are indexed from 0, so $a_i$ is `u_i 0` and $b_i$ is `u_i 1`.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:26, proof of Theorem 1.14, (29)

import Mathlib
import Definitions.Def_TensorNP_Rank_Defs
import Definitions.Def_TensorNP_Rank_Construction

namespace TensorNP.Rank

theorem eq29_iff_system30 :
    (∀ {E : Type} [Field E] {l m n : ℕ} (B : Fin l → Fin m → Fin n → E),
      rankOver E B ≤ 2 →
        ∃ (u₁ v₁ : Fin l → E) (u₂ v₂ : Fin m → E) (u₃ v₃ : Fin n → E),
          B = outer u₁ u₂ u₃ + outer v₁ v₂ v₃) ∧
    (∀ {K : Type} [Field K] [CharZero K] (u₁ u₂ u₃ v₁ v₂ v₃ : Fin 2 → K),
      ((fun i j k => (tensorA i j k : K)) = outer u₁ u₂ u₃ + outer v₁ v₂ v₃ ↔
        System30 (u₁ 0) (u₂ 0) (u₃ 0) (u₁ 1) (u₂ 1) (u₃ 1)
          (v₁ 0) (v₂ 0) (v₃ 0) (v₁ 1) (v₂ 1) (v₃ 1))) := by sorry

end TensorNP.Rank
