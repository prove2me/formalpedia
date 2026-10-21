-- Prove2me | Theorems.Thm_ParamSDO_Transition_ranks_maximal
-- name    : ParamSDO.Transition.ranks_maximal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:09.759415+00:00
-- url     : https://prove2.me/theorems/b8a82c13-9a71-4825-b53c-4c88f0aa6015
-- title:
--   Appendix, proof of Theorem 1, p. 22 — maximally complementary solutions have maximal ranks on 𝓟*(ϵ) × 𝓓*(ϵ)
-- statement:
--   In the setting of the parametric semidefinite pair $(\mathrm P_\epsilon)/(\mathrm D_\epsilon)$ with symmetric data, under Assumptions 1 and 2, fix $\epsilon\in\operatorname{int}(\mathcal E)$.
--
--   1. If $X\in\operatorname{ri}\mathcal P^*(\epsilon)$, then $\operatorname{rank}X'\le\operatorname{rank}X$ for every $X'\in\mathcal P^*(\epsilon)$, and $\operatorname{rank}X=\operatorname{rank}X^*(\epsilon)$.
--   2. If $(y,S)\in\operatorname{ri}\mathcal D^*(\epsilon)$, then $\operatorname{rank}S'\le\operatorname{rank}S$ for every $(y',S')\in\mathcal D^*(\epsilon)$, and $\operatorname{rank}S=\operatorname{rank}S^*(\epsilon)$.
--
--   $$
--   \operatorname{rank}X^*(\epsilon)=\max_{X'\in\mathcal P^*(\epsilon)}\operatorname{rank}X',\qquad
--   \operatorname{rank}S^*(\epsilon)=\max_{(y',S')\in\mathcal D^*(\epsilon)}\operatorname{rank}S'.
--   $$
--
--   Here $\operatorname{rank}X^*(\epsilon)$ and $\operatorname{rank}S^*(\epsilon)$ are the ranks of a maximally complementary optimal solution (Definition 1). The statement shows these ranks do not depend on which maximally complementary solution is chosen, so Definition 5 of a transition point is well posed.
--
--   **Formalization Note** $\operatorname{ri}$ is Mathlib's `intrinsicInterior`. $\operatorname{rank}X^*(\epsilon)$ is encoded as the supremum of the ranks over $\operatorname{ri}\mathcal P^*(\epsilon)$; part 1 says that supremum is attained at every relative-interior point. The symmetry of the data and Assumptions 1–2 are carried as hypotheses, although part of the claim is pure convex geometry.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 22, Appendix, proof of Theorem 1, first sentence (also p. 2, after Definition 1)

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem ranks_maximal {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar),
      (∀ X ∈ intrinsicInterior ℝ (Pstar A b C Cbar ϵ),
        (∀ X' ∈ Pstar A b C Cbar ϵ, X'.rank ≤ X.rank) ∧ X.rank = rkX A b C Cbar ϵ) ∧
      (∀ p ∈ intrinsicInterior ℝ (Dstar A b C Cbar ϵ),
        (∀ p' ∈ Dstar A b C Cbar ϵ, p'.2.rank ≤ p.2.rank) ∧ p.2.rank = rkS A b C Cbar ϵ) := by sorry

end ParamSDO.Transition
