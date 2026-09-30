-- Prove2me | Theorems.Thm_UnderstandingML_least_squares_normal_equations
-- name    : UnderstandingML.least_squares_normal_equations
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:55:06.535624+00:00
-- url     : https://prove2.me/theorems/edf9ee2a-f803-4dce-9eba-4e4ae86a2769
-- title:
--   §9.2.1 (Least Squares): the ERM problem for homogenous linear regression with the squared loss is solved exactly by the solutions of Aw = b, which exist
-- statement:
--   **§9.2.1 (Least Squares).** The ERM problem for the homogenous linear regression predictors with the squared loss is $\operatorname{argmin}_w \frac1m \sum_{i=1}^m (\langle w, x_i\rangle - y_i)^2$. Setting the gradient to zero rewrites it as $Aw = b$ with $A = \sum_i x_i x_i^\top$ and $b = \sum_i y_i x_i$ (9.6). We can always find a solution to $Aw = b$ because $b$ is in the range of $A$.
--
--   Formally: some $w$ solves $Aw = b$, and $w$ solves $Aw = b$ if and only if $h_w$ is an ERM hypothesis for the sample with respect to the squared loss over the homogenous linear class.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §9.2.1 pp. 124-125, Least Squares and Equation (9.6) with the argument that b is in the range of A

import Definitions.Def_UnderstandingML_Linear

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **§9.2.1, Least Squares** (pp. 124–125). The ERM problem for the homogenous linear
regression predictors with the squared loss, `argmin_w (1/m) ∑ᵢ (⟨w, xᵢ⟩ − yᵢ)²`, is solved by
the vectors `w` with `Aw = b`, `A = ∑ᵢ xᵢxᵢᵀ`, `b = ∑ᵢ yᵢxᵢ` (9.6): such a `w` always exists
(`b` is in the range of `A`), and `w` solves `Aw = b` if and only if `h_w` is an ERM
hypothesis. -/
theorem least_squares_normal_equations {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) :
    (∃ w : Vec d, gram x w = lsTarget x y) ∧
    ∀ w : Vec d, gram x w = lsTarget x y ↔
      IsERM squaredLoss (homLinear d) (fun i ↦ (x i, y i)) (affine w 0) := by sorry

end UnderstandingML
