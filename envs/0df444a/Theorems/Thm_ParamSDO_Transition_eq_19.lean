-- Prove2me | Theorems.Thm_ParamSDO_Transition_eq_19
-- name    : ParamSDO.Transition.eq_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:06.628991+00:00
-- url     : https://prove2.me/theorems/87e80fde-0b02-4314-bf53-937a619f4f98
-- title:
--   (19), Appendix, p. 22 — int(𝓔) is the union of the sets 𝓢_(θ,σ) over θ + σ ≤ n
-- statement:
--   In the setting of the parametric semidefinite pair $(\mathrm P_\epsilon)/(\mathrm D_\epsilon)$ with symmetric data, under Assumptions 1 and 2, let
--   $\mathcal S_{(\theta,\sigma)}$ be the set of $\epsilon\in\operatorname{int}(\mathcal E)$ for which some $(X,y,S)\in\operatorname{ri}(\mathcal P^*(\epsilon)\times\mathcal D^*(\epsilon))$ has $\operatorname{rank}X=\theta$ and $\operatorname{rank}S=\sigma$. Then
--   $$
--   \operatorname{int}(\mathcal E)=\bigcup_{\substack{\theta,\sigma\in\{0,\dots,n\}\\ \theta+\sigma\le n}}\mathcal S_{(\theta,\sigma)} .
--   \tag{19}
--   $$
--
--   Each $\epsilon$ in the interior of the domain thus carries a rank pair $(\theta,\sigma)$ of its optimal partition, and the interior is partitioned into finitely many level sets of that pair.
--
--   **Formalization Note** The union is over natural numbers $\theta,\sigma$ with $\theta+\sigma\le n$, which forces $\theta,\sigma\in\{0,\dots,n\}$. The symmetry of the data and Assumptions 1–2 are carried as hypotheses.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 22, Appendix, proof of Theorem 1, display (19)

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem eq_19 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    interior (domE A b C Cbar) = ⋃ (θ : ℕ) (σ : ℕ) (_ : θ + σ ≤ n), Srank A b C Cbar θ σ := by sorry

end ParamSDO.Transition
