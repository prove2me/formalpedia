-- Prove2me | Theorems.Thm_ParamSDO_Transition_transition_iff_frontier
-- name    : ParamSDO.Transition.transition_iff_frontier
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:09.614123+00:00
-- url     : https://prove2.me/theorems/d4dab236-a81c-4b11-b1c0-47622ab0a3c7
-- title:
--   Appendix, proof of Theorem 1, p. 22 — ϵ̄ is a transition point iff ϵ̄ ∈ bd(𝓢_(θ,σ)) ∩ int(𝓔) for some θ + σ ≤ n
-- statement:
--   In the setting of the parametric semidefinite pair $(\mathrm P_\epsilon)/(\mathrm D_\epsilon)$ with symmetric data, under Assumptions 1 and 2, with the sets $\mathcal S_{(\theta,\sigma)}\subseteq\operatorname{int}(\mathcal E)$ of the Appendix: for every $\bar\epsilon\in\mathbb R$,
--   $$
--   \bar\epsilon\ \text{is a transition point}\iff \bar\epsilon\in\operatorname{bd}\big(\mathcal S_{(\theta,\sigma)}\big)\cap\operatorname{int}(\mathcal E)\ \text{for some}\ \theta,\sigma\in\mathbb Z_{\ge0}\ \text{with}\ \theta+\sigma\le n .
--   $$
--
--   This turns the rank-change definition of a transition point (Definition 5) into a purely topological condition, which reduces Theorem 1 to counting boundary points of finitely many subsets of $\mathbb R$.
--
--   **Formalization Note** $\operatorname{bd}$ is the topological boundary (`frontier`) in $\mathbb R$. The symmetry of the data and Assumptions 1–2 are carried as hypotheses.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 22, Appendix, proof of Theorem 1, sentence after (19) and paragraph "Equivalency of boundary points and transition points"

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem transition_iff_frontier {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵbar : ℝ, IsTransitionPoint A b C Cbar ϵbar ↔
      ∃ θ σ : ℕ, θ + σ ≤ n ∧
        ϵbar ∈ frontier (Srank A b C Cbar θ σ) ∩ interior (domE A b C Cbar) := by sorry

end ParamSDO.Transition
