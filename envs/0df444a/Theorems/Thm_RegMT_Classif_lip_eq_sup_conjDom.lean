-- Prove2me | Theorems.Thm_RegMT_Classif_lip_eq_sup_conjDom
-- name    : RegMT.Classif.lip_eq_sup_conjDom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:21.624662+00:00
-- url     : https://prove2.me/theorems/47c04068-adab-4fd7-8e47-8e577d20f7fe
-- title:
--   Proof of Lemma A.3, pp. 30, 35 — modulus from conjugate slopes
-- statement:
--   For every convex Lipschitz continuous function $L:\mathbb R\to\mathbb R$, let $L^*(\theta)=\sup_z(\theta z-L(z))$ and $\Theta=\{\theta:L^*(\theta)<\infty\}$. Then
--   $$\operatorname{lip}(L)=\sup_{\theta\in\Theta}|\theta|.$$
--   This identifies the exact coefficient in the final constraint of program (18). The Lipschitz modulus is the least Lipschitz bound, rather than any chosen bound.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, pp. 30, 35, end of proof of Lemma A.3 and proof of Theorem 3.11

import Mathlib
import Definitions.Def_RegMT_Classif_Model

namespace RegMT.Classif

/-- The Lipschitz modulus is the supremum of the absolute slopes in the
effective domain of the conjugate, pp. 30 and 35. -/
theorem lip_eq_sup_conjDom (L : ℝ → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L) :
    WassersteinDRO.Duality.lipschitzModulus L = conjSlope L := by sorry

end RegMT.Classif
