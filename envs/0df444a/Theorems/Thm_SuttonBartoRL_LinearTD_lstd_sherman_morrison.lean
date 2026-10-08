-- Prove2me | Theorems.Thm_SuttonBartoRL_LinearTD_lstd_sherman_morrison
-- name    : SuttonBartoRL.LinearTD.lstd_sherman_morrison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:48:19.591804+00:00
-- url     : https://prove2.me/theorems/9e2b6493-6cb4-4e37-bb43-d894bf72be94
-- title:
--   Sherman–Morrison update of the LSTD inverse $\hat{\mathbf A}_t^{-1}$ (9.22)
-- statement:
--   Let $\mathbf x_0, \mathbf x_1, \dots \in \mathbb R^d$ be feature vectors, $\gamma, \varepsilon \in \mathbb R$, and $\hat{\mathbf A}_t = \sum_{k=0}^{t-1} \mathbf x_k(\mathbf x_k - \gamma \mathbf x_{k+1})^\top + \varepsilon \mathbf I$ the LSTD estimate (9.20). Let $t > 0$, suppose $\hat{\mathbf A}_{t-1}$ is invertible and
--
--   $$1 + (\mathbf x_{t-1} - \gamma \mathbf x_t)^\top \hat{\mathbf A}_{t-1}^{-1}\mathbf x_{t-1} \ne 0 .$$
--
--   Then $\hat{\mathbf A}_t = \hat{\mathbf A}_{t-1} + \mathbf x_{t-1}(\mathbf x_{t-1} - \gamma \mathbf x_t)^\top$, the matrix $\hat{\mathbf A}_t$ is invertible, and
--
--   $$\hat{\mathbf A}_t^{-1} = \hat{\mathbf A}_{t-1}^{-1} - \frac{\hat{\mathbf A}_{t-1}^{-1}\mathbf x_{t-1}(\mathbf x_{t-1} - \gamma \mathbf x_t)^\top \hat{\mathbf A}_{t-1}^{-1}}{1 + (\mathbf x_{t-1} - \gamma \mathbf x_t)^\top \hat{\mathbf A}_{t-1}^{-1}\mathbf x_{t-1}} .$$
--
--   This rank-one (Sherman–Morrison) update lets LSTD maintain $\hat{\mathbf A}_t^{-1}$ with $O(d^2)$ work per step instead of inverting a $d \times d$ matrix.
--
--   **Formalization Note** The index $t > 0$ is written $t + 1$ with $t \ge 0$, avoiding natural-number subtraction. Invertibility of $\hat{\mathbf A}_{t-1}$ and the nonzero denominator are hypotheses. The book also says that $\varepsilon \mathbf I$, "for some small $\varepsilon > 0$, ensures that $\hat{\mathbf A}_t$ is always invertible" (p. 229); that sentence is false in general, because the summands $\mathbf x_k(\mathbf x_k - \gamma\mathbf x_{k+1})^\top$ are not symmetric positive semidefinite (for $d = 1$, $\varepsilon = 1/10$, $\gamma = 1/2$, $\mathbf x_0 = 1$ and $\mathbf x_1 = 11/5$ one gets $\hat{\mathbf A}_1 = 1 \cdot (1 - 11/10) + 1/10 = 0$), and it is not part of the statement. The identity holds for every $\varepsilon$, which is a stronger statement than the book's $\varepsilon > 0$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (9.20), p. 228; Eq. (9.22), p. 229

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

namespace SuttonBartoRL.LinearTD

/-- Sutton & Barto (2018), (9.20) and (9.22), pp. 228–229: the Sherman–Morrison update of the LSTD
inverse. For `t > 0` (here `t + 1`), `Â_t = Â_{t−1} + x_{t−1}(x_{t−1} − γx_t)ᵀ`; if `Â_{t−1}` is
invertible and `1 + (x_{t−1} − γx_t)ᵀÂ_{t−1}⁻¹x_{t−1} ≠ 0`, then `Â_t` is invertible and
`Â_t⁻¹ = Â_{t−1}⁻¹ − Â_{t−1}⁻¹x_{t−1}(x_{t−1} − γx_t)ᵀÂ_{t−1}⁻¹ / (1 + (x_{t−1} − γx_t)ᵀÂ_{t−1}⁻¹x_{t−1})`. -/
theorem lstd_sherman_morrison {d : ℕ} (γ ε : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ)
    (hinv : IsUnit (lstdA γ ε x t).det)
    (hden : 1 + (x t - γ • x (t + 1)) ⬝ᵥ ((lstdA γ ε x t)⁻¹ *ᵥ x t) ≠ 0) :
    lstdA γ ε x (t + 1) = lstdA γ ε x t + vecMulVec (x t) (x t - γ • x (t + 1)) ∧
      IsUnit (lstdA γ ε x (t + 1)).det ∧
      (lstdA γ ε x (t + 1))⁻¹ =
        (lstdA γ ε x t)⁻¹ -
          (1 + (x t - γ • x (t + 1)) ⬝ᵥ ((lstdA γ ε x t)⁻¹ *ᵥ x t))⁻¹ •
            ((lstdA γ ε x t)⁻¹ * vecMulVec (x t) (x t - γ • x (t + 1)) * (lstdA γ ε x t)⁻¹) := by sorry

end SuttonBartoRL.LinearTD
