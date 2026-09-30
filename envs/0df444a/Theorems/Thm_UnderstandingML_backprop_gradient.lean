-- Prove2me | Theorems.Thm_UnderstandingML_backprop_gradient
-- name    : UnderstandingML.backprop_gradient
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:06:27.820732+00:00
-- url     : https://prove2.me/theorems/b95b18eb-8ef4-40ad-9a0e-4527c3705fe3
-- title:
--   §20.6: backpropagation computes the gradient: ∂(½‖o_T − y‖²)/∂w_{(v_{t,j},v_{t+1,i})} = δ_{t+1,i} σ'(a_{t+1,i}) o_{t,j} for differentiable σ
-- statement:
--   **Backpropagation calculates the gradient (§20.6).** For a layered graph, a differentiable activation $\sigma$, an example $(x, y)$ and the squared loss $\tfrac12\|o_T - y\|^2$, let the forward pass compute $a_t = W_{t-1}o_{t-1}$, $o_t = \sigma(a_t)$ and the backward pass $\delta_T = o_T - y$, $\delta_t = \delta_{t+1}\operatorname{diag}(\sigma'(a_{t+1}))W_t$. Then for every edge $(v_{t,j}, v_{t+1,i}) \in E$, the partial derivative of the loss with respect to the weight of that edge, all other weights fixed, is $\delta_{t+1,i}\,\sigma'(a_{t+1,i})\,o_{t,j}$ (Equation (20.3), with the book's layer indices shifted by one).
--
--   Formally: `HasDerivAt` of the loss as a function of the one weight, at its current value.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §20.6 pp. 278-281, the backpropagation pseudocode and Equation (20.3)

import Definitions.Def_UnderstandingML_NeuralNetworks

open MeasureTheory

namespace UnderstandingML

/-- **Backpropagation computes the gradient** (§20.6, pp. 279–281, "We have thus shown that the
pseudocode of backpropagation indeed calculates the gradient"). For a layered graph with a
differentiable activation `σ`, the squared loss `½‖o_T − y‖²` on the example `(x, y)`, and an
edge `(v_{t,j}, v_{t+1,i}) ∈ E`, the partial derivative of the loss with respect to the weight
of that edge, all other weights fixed, is `δ_{t+1,i} σ'(a_{t+1,i}) o_{t,j}` (20.3), where the
`δ` are computed by the backward pass `δ_T = o_T − y`,
`δ_t = δ_{t+1} diag(σ'(a_{t+1})) W_t`. -/
theorem backprop_gradient (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (G : LayeredGraph)
    (w : ℕ → ℕ → ℕ → ℝ) (x y : ℕ → ℝ) (t i j : ℕ) (ht : t < G.depth) (he : (i, j) ∈ G.edges t) :
    HasDerivAt (fun s ↦ netLoss σ G (updateWeight w t i j s) x y)
      (backDelta σ G w x y (t + 1) i * deriv σ (netInput σ G w x t i) * netOutput σ G w x t j)
      (w t i j) := by sorry

end UnderstandingML
