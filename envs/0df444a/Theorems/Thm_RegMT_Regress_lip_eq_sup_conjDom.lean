-- Prove2me | Theorems.Thm_RegMT_Regress_lip_eq_sup_conjDom
-- name    : RegMT.Regress.lip_eq_sup_conjDom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:36.226992+00:00
-- url     : https://prove2.me/theorems/5a71c83c-862e-4a13-8200-3a6334fcf29b
-- title:
--   Proof of Lemma A.3, p. 30 — lip(L) = sup{|θ| : L*(θ) < ∞} for convex Lipschitz L
-- statement:
--   Let $L:\mathbb R\to\mathbb R$ be nonnegative, convex and Lipschitz continuous, with convex conjugate $L^*(\theta)=\sup_{z}\theta z-L(z)$ and effective domain $\Theta=\{\theta\in\mathbb R:L^*(\theta)<\infty\}$. Then the Lipschitz modulus $\mathrm{lip}(L)=\sup_{z\neq z'}|L(z)-L(z')|/|z-z'|$ satisfies
--
--   $$
--   \mathrm{lip}(L)\;=\;\sup\{|\theta|:\ \theta\in\Theta\}=\sup_{\theta}\{|\theta|:L^*(\theta)<\infty\}.
--   $$
--
--   This identity closes the proof of Lemma A.3. There, the conjugate representation $L(t)=\sup_{\theta\in\Theta}\theta t-L^*(\theta)$ gives the condition $\sup_{\theta\in\Theta}|\theta|\cdot\|\beta\|_*\le\gamma$, and the identity turns it into the condition $\mathrm{lip}(L)\|\beta\|_*\le\gamma$ of the lemma.
--
--   **Formalization Note.** Both sides take values in $[0,\infty]$. $\mathrm{lip}(L)$ is the published `lipschitzModulus`, and $\Theta$ is `conjDom L`, in which $L^*(\theta)<\infty$ is written as boundedness above of $z\mapsto\theta z-L(z)$. The supremum over $\Theta$ is the supremum in $[0,\infty]$, so it is $0$ if $\Theta$ is empty. For convex Lipschitz $L$, $\Theta$ is never empty.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, pp. 29–30, proof of Lemma A.3 (definition of Θ, p. 30 line 1; closing sentence, p. 30)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus
import Definitions.Def_RegMT_Regress_Model

namespace RegMT.Regress

/-- End of the proof of Lemma A.3, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani,
*Regularization via Mass Transportation*, arXiv:1710.10016v3, p. 30: for a convex, Lipschitz
continuous `L : ℝ → ℝ`, the Lipschitz modulus `lip(L)` (§1.1, p. 4) equals
`sup {|θ| : L*(θ) < ∞}`, the largest absolute value in the effective domain
`Θ = RegMT.Classif.conjDom L` of the convex conjugate `L*`. Both sides are in `ℝ≥0∞`.
The nonnegativity hypothesis carries §2.1's definition of a loss into this proof step. -/
theorem lip_eq_sup_conjDom (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L)
    (h_nonneg : ∀ z, 0 ≤ L z) (hLip : ∃ K, LipschitzWith K L) :
    WassersteinDRO.Duality.lipschitzModulus L = ⨆ θ ∈ RegMT.Classif.conjDom L, ENNReal.ofReal |θ| := by sorry

end RegMT.Regress
