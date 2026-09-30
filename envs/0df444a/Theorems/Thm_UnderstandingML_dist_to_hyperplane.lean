-- Prove2me | Theorems.Thm_UnderstandingML_dist_to_hyperplane
-- name    : UnderstandingML.dist_to_hyperplane
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:37:23.056749+00:00
-- url     : https://prove2.me/theorems/af360d02-e416-4a4e-9f7f-7d2ed8bad02c
-- title:
--   Claim 15.1: the distance from x to the hyperplane {v : ⟨w,v⟩ + b = 0} with ‖w‖ = 1 is |⟨w,x⟩ + b|
-- statement:
--   **Claim 15.1.** The distance between a point $x$ and the hyperplane defined by $(w, b)$ where $\|w\| = 1$ is $|\langle w, x\rangle + b|$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.1 p. 203, Claim 15.1 with its proof

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Claim 15.1** (p. 203). The distance between a point `x` and the hyperplane defined by
`(w, b)` where `‖w‖ = 1` is `|⟨w, x⟩ + b|`. -/
theorem dist_to_hyperplane {d : ℕ} (w : Vec d) (hw : ‖w‖ = 1) (b : ℝ) (x : Vec d) :
    Metric.infDist x {v : Vec d | ⟪w, v⟫_ℝ + b = 0} = |⟪w, x⟫_ℝ + b| := by sorry

end UnderstandingML
