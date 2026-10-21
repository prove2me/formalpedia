-- Prove2me | Theorems.Thm_ParamSDO_Transition_strong_duality
-- name    : ParamSDO.Transition.strong_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:08.178267+00:00
-- url     : https://prove2.me/theorems/f8a6233f-4773-498f-ba73-ad334a9ef811
-- title:
--   p. 2, after Remark 1 — strong duality: 𝓟*(ϵ) and 𝓓*(ϵ) are nonempty and compact for every ϵ ∈ int(𝓔)
-- statement:
--   In the setting of the parametric semidefinite pair $(\mathrm P_\epsilon)/(\mathrm D_\epsilon)$ with symmetric data, under Assumptions 1 and 2, for every $\epsilon\in\operatorname{int}(\mathcal E)$ the primal and dual optimal sets
--   $$
--   \mathcal P^*(\epsilon)=\{X\in\mathcal P:\ \langle C+\epsilon\bar C,X\rangle=v(\epsilon)\},\qquad
--   \mathcal D^*(\epsilon)=\{(y,S)\in\mathcal D(\epsilon):\ b^Ty=v(\epsilon)\}
--   $$
--   are nonempty and compact.
--
--   Since $\mathcal D^*(\epsilon)$ consists of the dual feasible points whose objective equals the *primal* optimal value, its nonemptiness is exactly strong duality in the paper's sense: both optimal values are attained and the duality gap is zero.
--
--   **Formalization Note** Compactness is with respect to the product topology on $\mathbb R^{n\times n}$ and on $\mathbb R^m\times\mathbb R^{n\times n}$. The symmetry of the data and Assumptions 1–2 are carried as hypotheses.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 2, paragraph after Remark 1

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem strong_duality {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar),
      (Pstar A b C Cbar ϵ).Nonempty ∧ IsCompact (Pstar A b C Cbar ϵ) ∧
        (Dstar A b C Cbar ϵ).Nonempty ∧ IsCompact (Dstar A b C Cbar ϵ) := by sorry

end ParamSDO.Transition
