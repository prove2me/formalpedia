-- Prove2me | Theorems.Thm_RegMT_Classif_lemma_A_3
-- name    : RegMT.Classif.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:28.560353+00:00
-- url     : https://prove2.me/theorems/633e8e77-94dc-4b58-a9fb-911788f1d58e
-- title:
--   Lemma A.3, p. 29 — convex Lipschitz loss against a norm penalty
-- statement:
--   Let $L:\mathbb R\to\mathbb R$ be convex and Lipschitz continuous. Let $\beta$ be a continuous linear functional on a finite-dimensional real normed space, let $\hat\zeta$ be a point of that space, and let $\gamma>0$. Then
--   $$\sup_\zeta\bigl\{L(\langle\beta,\zeta\rangle)-\gamma\|\zeta-\hat\zeta\|\bigr\}=\begin{cases}L(\langle\beta,\hat\zeta\rangle),&\operatorname{lip}(L)\|\beta\|_*\le\gamma,\\+\infty,&\text{otherwise.}\end{cases}$$
--   This evaluates each feature supremum in the label-split reformulation. The dual norm is the operator norm induced by the same norm used in the transport cost.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, pp. 29–30, Lemma A.3

import Mathlib
import Definitions.Def_RegMT_Classif_Model

namespace RegMT.Classif

/-- Lemma A.3, p. 29: the supremum of a convex Lipschitz loss minus a norm
penalty is either its value at the center or positive infinity. -/
theorem lemma_A_3 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : ℝ → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L)
    (β : V →L[ℝ] ℝ) (ζhat : V) (γ : ℝ) (hγ : 0 < γ) :
    (⨆ ζ : V, ((L (β ζ) - γ * ‖ζ - ζhat‖ : ℝ) : EReal)) =
      if (WassersteinDRO.Duality.lipschitzModulus L).toReal * ‖β‖ ≤ γ
      then ((L (β ζhat) : ℝ) : EReal) else ⊤ := by sorry

end RegMT.Classif
