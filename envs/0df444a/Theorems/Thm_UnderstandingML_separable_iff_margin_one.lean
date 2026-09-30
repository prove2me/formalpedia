-- Prove2me | Theorems.Thm_UnderstandingML_separable_iff_margin_one
-- name    : UnderstandingML.separable_iff_margin_one
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:53:31.543928+00:00
-- url     : https://prove2.me/theorems/c82feb2a-0f28-40b9-95fd-2c9d76dc1f54
-- title:
--   §9.1.1, Equation (9.1): a sample is separable iff some w has yᵢ⟨w, xᵢ⟩ ≥ 1 for all i
-- statement:
--   **§9.1.1, Equation (9.1).** In the realizable case we look for $w$ with $y_i\langle w, x_i\rangle > 0$ for all $i$. If $w^*$ satisfies this, $\gamma = \min_i y_i\langle w^*, x_i\rangle$ and $\bar w = w^*/\gamma$, then $y_i\langle \bar w, x_i\rangle \ge 1$ for all $i$ (9.1); and clearly such a vector is an ERM predictor.
--
--   Formally: the sample $(x_i, y_i)$ is separable if and only if there is $w$ with $y_i\langle w, x_i\rangle \ge 1$ for all $i$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §9.1.1 p. 119, the derivation of Equation (9.1)

import Definitions.Def_UnderstandingML_Linear

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **§9.1.1, Equation (9.1)** (p. 119). In the realizable (separable) case there is a vector
with `yᵢ⟨w, xᵢ⟩ ≥ 1` for all `i` (scale a separating vector by `1/γ`, `γ = minᵢ yᵢ⟨w*, xᵢ⟩`),
and clearly such a vector separates the sample: separability is equivalent to the feasibility
of the linear constraints (9.1). -/
theorem separable_iff_margin_one {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) :
    Separable x y ↔ ∃ w : Vec d, ∀ i, 1 ≤ y i * ⟪w, x i⟫_ℝ := by sorry

end UnderstandingML
