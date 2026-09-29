-- Prove2me | Theorems.Thm_SPOBounds_Margin_spo_loss_lipschitz_like
-- name    : SPOBounds.Margin.spo_loss_lipschitz_like
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:33:24.030983+00:00
-- url     : https://prove2.me/theorems/2d642aff-3f93-45c0-8498-000cface3588
-- title:
--   Theorem 3(b) — the SPO loss is Lipschitz-like away from degeneracy
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, and let $S\subseteq E$ be nonempty, compact, convex and not a singleton. Let $w^*$ be any optimization oracle for $S$, and suppose $S$ satisfies the strength property with parameter $\mu>0$. Then for every fixed cost vector $c$ and all $\hat c_1,\hat c_2$,
--   $$|\ell_{\rm SPO}(\hat c_1,c)-\ell_{\rm SPO}(\hat c_2,c)| \;\le\; \Big(\frac{\|c\|_*}{\mu\cdot\min\{\nu_S(\hat c_1),\nu_S(\hat c_2)\}}\Big)\,\|\hat c_1-\hat c_2\|_* ,$$
--   where the right-hand side is read as $+\infty$ when the minimum is zero.
--
--   The SPO loss is discontinuous at degenerate predictions; this result quantifies its regularity away from them.
--
--   **Formalization Note** Stated multiplied out: $\mu\min\{\nu_S(\hat c_1),\nu_S(\hat c_2)\}\,|\ell_{\rm SPO}(\hat c_1,c)-\ell_{\rm SPO}(\hat c_2,c)|\le\|c\|_*\,\|\hat c_1-\hat c_2\|_*$, equivalent to the displayed form when the minimum is positive and trivially true when it is zero.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 16, Theorem 3(b)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

namespace SPOBounds.Margin

/-- **Theorem 3(b)** (arXiv:1905.11488v3, p. 16). Under the strength property with parameter
`μ > 0` (nonempty, compact, convex, non-singleton `S`, any oracle `w`), for every fixed cost
vector `c` and all `ĉ₁, ĉ₂`,
`|ℓ_SPO(ĉ₁, c) − ℓ_SPO(ĉ₂, c)| ≤ (‖c‖_* / (μ · min{ν_S(ĉ₁), ν_S(ĉ₂)})) ‖ĉ₁ − ĉ₂‖_*`,
stated multiplied out (the paper reads the right-hand side as `+∞` when the minimum is `0`). -/
theorem spo_loss_lipschitz_like {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSc : IsCompact S) (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * |spoLoss w c₁ c - spoLoss w c₂ c| ≤
      ‖c‖ * ‖c₁ - c₂‖ := by sorry

end SPOBounds.Margin
