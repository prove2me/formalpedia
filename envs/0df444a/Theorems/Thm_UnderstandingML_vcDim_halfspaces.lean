-- Prove2me | Theorems.Thm_UnderstandingML_vcDim_halfspaces
-- name    : UnderstandingML.vcDim_halfspaces
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:54:42.076402+00:00
-- url     : https://prove2.me/theorems/3f64a576-cd61-4d8b-b5f6-ae1310829c7d
-- title:
--   Theorem 9.3: the VC-dimension of the class of nonhomogenous halfspaces in ℝ^d is d + 1
-- statement:
--   **Theorem 9.3.** The VC dimension of the class of nonhomogenous halfspaces in $\mathbb{R}^d$ is $d + 1$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §9.1.3 p. 122, Theorem 9.3 with its proof

import Definitions.Def_UnderstandingML_Linear

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 9.3** (p. 122). The VC dimension of the class of nonhomogenous halfspaces in `ℝ^d`
is `d + 1`. -/
theorem vcDim_halfspaces (d : ℕ) : vcDim (halfspaces d) = d + 1 := by sorry

end UnderstandingML
