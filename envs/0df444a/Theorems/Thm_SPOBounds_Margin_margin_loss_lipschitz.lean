-- Prove2me | Theorems.Thm_SPOBounds_Margin_margin_loss_lipschitz
-- name    : SPOBounds.Margin.margin_loss_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:33:49.531248+00:00
-- url     : https://prove2.me/theorems/71dfcbfc-d0c3-44e7-bf1e-b6728cd89510
-- title:
--   Theorem 3(c) — the $\gamma$-margin SPO loss is $\frac{1}{\gamma\mu}(\|c\|_*+\mu\,\omega_S(c))$-Lipschitz
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, and let $S\subseteq E$ be nonempty, compact, convex and not a singleton. Let $w^*$ be any optimization oracle for $S$, and suppose $S$ satisfies the strength property with parameter $\mu>0$. Then for every fixed cost vector $c$ and every $\gamma>0$, the $\gamma$-margin SPO loss is Lipschitz in the prediction with respect to the dual norm:
--   $$|\ell^\gamma_{\rm mSPO}(\hat c_1,c)-\ell^\gamma_{\rm mSPO}(\hat c_2,c)| \;\le\; \Big(\frac{\|c\|_*+\mu\cdot\omega_S(c)}{\gamma\mu}\Big)\,\|\hat c_1-\hat c_2\|_* \qquad\text{for all } \hat c_1,\hat c_2 .$$
--
--   Unlike the SPO loss, the margin SPO loss is globally Lipschitz; this is what allows a contraction inequality to transfer the Rademacher complexity of the loss class to that of the hypothesis class.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 16, Theorem 3(c)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

namespace SPOBounds.Margin

/-- **Theorem 3(c)** (arXiv:1905.11488v3, p. 16). Under the strength property with parameter
`μ > 0` (nonempty, compact, convex, non-singleton `S`, any oracle `w`), for every fixed cost
vector `c` and every `γ > 0`, the `γ`-margin SPO loss is
`(‖c‖_* + μ ω_S(c)) / (γ μ)`-Lipschitz in its first argument with respect to the dual norm:
`|ℓ^γ_mSPO(ĉ₁, c) − ℓ^γ_mSPO(ĉ₂, c)| ≤ ((‖c‖_* + μ ω_S(c)) / (γ μ)) ‖ĉ₁ − ĉ₂‖_*`. -/
theorem margin_loss_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSc : IsCompact S) (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (γ : ℝ) (hγ : 0 < γ) (c c₁ c₂ : StrongDual ℝ E) :
    |marginLoss S w γ c₁ c - marginLoss S w γ c₂ c| ≤
      (‖c‖ + μ * omega S c) / (γ * μ) * ‖c₁ - c₂‖ := by sorry

end SPOBounds.Margin
