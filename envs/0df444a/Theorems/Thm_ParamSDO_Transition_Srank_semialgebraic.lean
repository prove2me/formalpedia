-- Prove2me | Theorems.Thm_ParamSDO_Transition_Srank_semialgebraic
-- name    : ParamSDO.Transition.Srank_semialgebraic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:16.080758+00:00
-- url     : https://prove2.me/theorems/257443ab-2026-4b00-ba80-2d153a55f448
-- title:
--   Appendix, proof of Theorem 1, p. 23 — each 𝓢_(θ,σ) is a semi-algebraic subset of ℝ
-- statement:
--   In the setting of the parametric semidefinite pair $(\mathrm P_\epsilon)/(\mathrm D_\epsilon)$ with symmetric data, under Assumptions 1 and 2, for all natural numbers $\theta,\sigma$ the set
--   $$
--   \mathcal S_{(\theta,\sigma)}=\big\{\epsilon\in\mathbb R:\ \exists\,(X,y,S)\in\operatorname{ri}(\mathcal P^*(\epsilon)\times\mathcal D^*(\epsilon)),\ \operatorname{rank}X=\theta,\ \operatorname{rank}S=\sigma,\ \epsilon\in\operatorname{int}(\mathcal E)\big\}
--   $$
--   is a semi-algebraic subset of $\mathbb R$: a finite union of sets of the form $\{p_1=\dots=p_k=0,\ g_1<0,\dots,g_l<0\}$ with real polynomials $p_i,g_j$ in one variable.
--
--   Together with the finiteness of the boundary of a semi-algebraic subset of $\mathbb R$, this is the second half of the proof of Theorem 1.
--
--   **Formalization Note** A subset of $\mathbb R$ is encoded as a subset of $\mathbb R^1$ (`Fin 1 → ℝ`). The polynomials may have real coefficients, so the data enter as coefficients. The symmetry of the data and Assumptions 1–2 are carried as hypotheses.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 23, Appendix, proof of Theorem 1, conclusion of "Semi-algebraicity of S_(θ,σ)"

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem Srank_semialgebraic {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ θ σ : ℕ, IsSemialgebraicReal (Srank A b C Cbar θ σ) := by sorry

end ParamSDO.Transition
