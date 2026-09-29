-- Prove2me | Theorems.Thm_SPOBounds_Margin_oracle_lipschitz_like
-- name    : SPOBounds.Margin.oracle_lipschitz_like
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:32:44.958658+00:00
-- url     : https://prove2.me/theorems/a7c692ce-63e0-4688-810f-b14ddd20a936
-- title:
--   Theorem 3(a) — the optimization oracle is Lipschitz-like away from degeneracy
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, and let $S\subseteq E$ be nonempty, compact, convex and not a singleton. Let $w^*$ be any optimization oracle for $S$, and suppose $S$ satisfies the strength property with parameter $\mu>0$. Then for all cost vectors $\hat c_1,\hat c_2$,
--   $$\|w^*(\hat c_1) - w^*(\hat c_2)\| \;\le\; \Big(\frac{1}{\mu\cdot\min\{\nu_S(\hat c_1),\nu_S(\hat c_2)\}}\Big)\,\|\hat c_1-\hat c_2\|_* ,$$
--   where the right-hand side is read as $+\infty$ when $\min\{\nu_S(\hat c_1),\nu_S(\hat c_2)\}=0$.
--
--   Away from the degenerate cost vectors, the oracle's decision moves continuously with the prediction, at a rate inversely proportional to the distance to degeneracy. This is the base of the Lipschitz estimates for the SPO and margin SPO losses.
--
--   **Formalization Note** The inequality is stated multiplied out, $\mu\min\{\nu_S(\hat c_1),\nu_S(\hat c_2)\}\,\|w^*(\hat c_1)-w^*(\hat c_2)\|\le\|\hat c_1-\hat c_2\|_*$, which is equivalent when the minimum is positive and trivially true (as in the paper's convention) when it is zero; Lean's $1/0=0$ would otherwise make the statement false.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 16, Theorem 3(a)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

namespace SPOBounds.Margin

/-- **Theorem 3(a)** (arXiv:1905.11488v3, p. 16). Let `S` be a nonempty, compact, convex,
non-singleton feasible region in a finite-dimensional normed space, `w` any optimization oracle,
and suppose `S` satisfies the strength property with parameter `μ > 0`. Then for all cost
vectors `ĉ₁, ĉ₂`,
`‖w*(ĉ₁) − w*(ĉ₂)‖ ≤ (1 / (μ · min{ν_S(ĉ₁), ν_S(ĉ₂)})) ‖ĉ₁ − ĉ₂‖_*`,
stated multiplied out (the paper reads the right-hand side as `+∞` when the minimum is `0`). -/
theorem oracle_lipschitz_like {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSc : IsCompact S) (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * ‖w c₁ - w c₂‖ ≤ ‖c₁ - c₂‖ := by sorry

end SPOBounds.Margin
