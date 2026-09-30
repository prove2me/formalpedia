-- Prove2me | Theorems.Thm_UnderstandingML_hinge_lipschitz
-- name    : UnderstandingML.hinge_lipschitz
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:39:26.695382+00:00
-- url     : https://prove2.me/theorems/a7f32e27-660a-4c3d-a289-5ca12a76b218
-- title:
--   Claim 15.6: for y ∈ {±1}, w ↦ max{0, 1 − y⟨w,x⟩} is ‖x‖-Lipschitz
-- statement:
--   **Claim 15.6.** Let $f(w) = \max\{0, 1 - y\langle w, x\rangle\}$. Then $f$ is $\|x\|$-Lipschitz.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.2.1 p. 208, Claim 15.6

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Claim 15.6** (p. 208). Let `f(w) = max{0, 1 − y⟨w, x⟩}` with `y ∈ {±1}`. Then `f` is
`‖x‖`-Lipschitz. -/
theorem hinge_lipschitz {d : ℕ} (x : Vec d) (y : ℝ) (hy : y = 1 ∨ y = -1) :
    ∀ w₁ w₂ : Vec d, |hingeLoss w₁ (x, y) - hingeLoss w₂ (x, y)| ≤ ‖x‖ * ‖w₁ - w₂‖ := by sorry

end UnderstandingML
