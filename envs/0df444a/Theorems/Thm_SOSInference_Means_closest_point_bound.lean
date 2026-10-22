-- Prove2me | Theorems.Thm_SOSInference_Means_closest_point_bound
-- name    : SOSInference.Means.closest_point_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:06.929789+00:00
-- url     : https://prove2.me/theorems/ef23149f-6ba2-43b1-87b8-0ed60bb74941
-- title:
--   §7.2.1 — closest-point bound: $\inf_a\{-\lambda^{\mathsf T}a+\|x-a\|_2^2\}=-\lambda^{\mathsf T}x-\|\lambda\|_2^2/4$
-- statement:
--   For $x,\lambda\in\mathbb R^l$:
--
--   1. $\displaystyle\inf_{a\in\mathbb R^l}\big\{-\lambda^{\mathsf T}a+\|x-a\|_2^2\big\}=-\lambda^{\mathsf T}x-\frac{\|\lambda\|_2^2}{4}$, and the infimum is a minimum;
--   2. the minimum is attained at the optimizer $a_*(x,\lambda)=x+\lambda/2$;
--   3. consequently, for every finite nonempty family $(z_j)$ of points of $\mathbb R^l$,
--   $$\inf_j\big\{-\lambda^{\mathsf T}z_j+\|x-z_j\|_2^2\big\}\ \ge\ -\lambda^{\mathsf T}x-\frac{\|\lambda\|_2^2}{4}.$$
--
--   It identifies the centre $x+\lambda/2$ around which the nearest sample points determine the constraints of the dual problem (22).
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 38, §7.2.1 (Step 1)

import Mathlib
import Definitions.Def_SOSInference_Means_sos

namespace SOSInference.Means

open scoped RealInnerProductSpace

/-- **Closest-point bound**, §7.2.1, p. 38 (Blanchet, Kang, Sample Out-of-Sample Inference Based on
Wasserstein Distance, arXiv:1605.01340v4, p. 38, Step 1).

For `x, λ ∈ ℝ^l`:
1. `inf_{a ∈ ℝ^l} {−λᵀa + ‖x − a‖₂²} = −λᵀx − ‖λ‖₂²/4`, and the infimum is a minimum;
2. it is attained at the optimizer `a*(x, λ) = x + λ/2`;
3. hence for every finite nonempty family `(z_j)`,
   `inf_j {−λᵀz_j + ‖x − z_j‖₂²} ≥ −λᵀx − ‖λ‖₂²/4`. -/
theorem closest_point_bound {l : ℕ} (x lam : E l) :
    IsLeast (Set.range fun a : E l => -⟪lam, a⟫ + ‖x - a‖ ^ 2) (-⟪lam, x⟫ - ‖lam‖ ^ 2 / 4) ∧
    -⟪lam, x + (1 / 2 : ℝ) • lam⟫ + ‖x - (x + (1 / 2 : ℝ) • lam)‖ ^ 2 =
      -⟪lam, x⟫ - ‖lam‖ ^ 2 / 4 ∧
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → E l),
      -⟪lam, x⟫ - ‖lam‖ ^ 2 / 4 ≤ ⨅ j, (-⟪lam, z j⟫ + ‖x - z j‖ ^ 2) := by sorry

end SOSInference.Means
