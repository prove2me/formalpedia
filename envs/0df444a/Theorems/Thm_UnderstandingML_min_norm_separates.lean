-- Prove2me | Theorems.Thm_UnderstandingML_min_norm_separates
-- name    : UnderstandingML.min_norm_separates
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T06:02:29.669421+00:00
-- url     : https://prove2.me/theorems/9b662221-aacf-4a3b-be7d-48ba2a9142e4
-- title:
--   §30.2.2: the point of the convex hull of separable signed examples closest to the origin separates them, ⟨w, vᵢ⟩ > 0 for all i
-- statement:
--   **§30.2.2 (p. 413).** Since the data is linearly separable, the convex hull of $\{x_1, \dots, x_m\}$ (all labels positive w.l.o.g.) does not contain the origin. Consider the point $w$ in this convex hull closest to the origin. We claim that $w$ separates the data: if $\langle w, x_i\rangle \le 0$ for some $i$, then $w' = (1-\alpha)w + \alpha x_i$ with $\alpha = \|w\|^2/(\|x_i\|^2 + \|w\|^2)$ is in the hull and has $\|w'\| < \|w\|$, a contradiction.
--
--   Formally: for $w$ of minimal norm in the convex hull of $v_1, \dots, v_m$ with $0$ not in the hull, $\langle w, v_i\rangle > 0$ for all $i$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §30.2.2 p. 413, the claim that the minimal-norm point of the convex hull separates the data, with its proof

import Definitions.Def_UnderstandingML_Compression

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **§30.2.2** (p. 413). For linearly separable data (`0` is not in the convex hull of the
signed examples `v₁, …, v_m`), the point `w` of the convex hull closest to the origin separates
the data: `⟨w, vᵢ⟩ > 0` for all `i`. -/
theorem min_norm_separates {d m : ℕ} (v : Fin m → Vec d) (w : Vec d)
    (hw : w ∈ convexHull ℝ (Set.range v)) (hmin : ∀ u ∈ convexHull ℝ (Set.range v), ‖w‖ ≤ ‖u‖)
    (h0 : (0 : Vec d) ∉ convexHull ℝ (Set.range v)) (i : Fin m) :
    0 < ⟪w, v i⟫_ℝ := by sorry

end UnderstandingML
