-- Prove2me | Theorems.Thm_UnderstandingML_projection_lemma
-- name    : UnderstandingML.projection_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:26:08.801986+00:00
-- url     : https://prove2.me/theorems/d6f0a757-71be-4547-86ce-fbbeed222dc4
-- title:
--   Lemma 14.9 (projection lemma): for the projection v of w onto a convex H and every u ∈ H, ‖w − u‖² − ‖v − u‖² ≥ 0
-- statement:
--   **Lemma 14.9 (Projection Lemma).** Let $H$ be a closed convex set and let $v$ be the projection of $w$ onto $H$, $v = \operatorname{argmin}_{x \in H}\|x - w\|^2$. Then for every $u \in H$, $\|w - u\|^2 - \|v - u\|^2 \ge 0$.
--
--   Formally: for a convex $H$ and a point $v \in H$ minimizing $\|x - w\|$ over $H$ (closedness only guarantees existence).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.4.1 pp. 193-194, Lemma 14.9 with its proof

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 14.9 (Projection Lemma)** (p. 193). Let `H` be a closed convex set and let `v` be the
projection of `w` onto `H`, `v = argmin_{x ∈ H} ‖x − w‖²`. Then for every `u ∈ H`,
`‖w − u‖² − ‖v − u‖² ≥ 0`. (Closedness is only needed for the projection to exist.) -/
theorem projection_lemma {d : ℕ} (H : Set (Vec d)) (hH : Convex ℝ H) (w v : Vec d)
    (hv : IsProjection H w v) (u : Vec d) (hu : u ∈ H) :
    0 ≤ ‖w - u‖ ^ 2 - ‖v - u‖ ^ 2 := by sorry

end UnderstandingML
