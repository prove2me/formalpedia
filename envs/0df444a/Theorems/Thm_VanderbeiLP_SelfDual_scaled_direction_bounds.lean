-- Prove2me | Theorems.Thm_VanderbeiLP_SelfDual_scaled_direction_bounds
-- name    : VanderbeiLP.SelfDual.scaled_direction_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:53:31.967153+00:00
-- url     : https://prove2.me/theorems/6c706032-e2b4-406b-ab23-5126e070c4bb
-- title:
--   Lemma 22.4 — bounds on the scaled step directions $p$, $q$, $r = p + q$
-- statement:
--   Let $n \ge 2$, let $A$ be a real skew-symmetric $n \times n$ matrix, let $x, z \in \mathbb{R}^n$ with $x > 0$ and $z > 0$ componentwise, let $0 \le \delta \le 1$, and let $(\Delta x, \Delta z)$ solve (22.5)–(22.6) at $(x, z)$. Define the scaled directions (22.11)
--
--   $$p = X^{-1/2}Z^{1/2}\Delta x, \qquad q = X^{1/2}Z^{-1/2}\Delta z, \qquad r = p + q,$$
--
--   let $P = \operatorname{diag}(p)$, $Q = \operatorname{diag}(q)$, and let $\mu = \frac1n x^T z$. With $\|\cdot\|$ the Euclidean norm:
--
--   1. $\|PQe\| \le \frac12\|r\|^2$;
--   2. if $\delta = 0$, then $\|r\|^2 = n\mu$;
--   3. if $\delta = 1$ and $(x, z) \in \mathcal N(\beta)$ for some $0 \le \beta < 1$, then
--   $$\|r\|^2 \le \frac{\beta^2\mu}{1 - \beta}.$$
--
--   Since $PQe = \Delta X\Delta Ze$, part (1) bounds the quadratic term of Theorem 22.2(4); parts (2) and (3) evaluate that bound for the predictor ($\delta = 0$) and the corrector ($\delta = 1$) steps.
--
--   **Formalization Note** $PQe$ is the vector with components $p_j q_j$. In (3) the book leaves $\beta < 1$ implicit (it divides by $1 - \beta$); it is stated as a hypothesis.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 328, Lemma 22.4 and Eq. (22.11) (PDF p. 334)

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

open Matrix

namespace VanderbeiLP.SelfDual

/-- Lemma 22.4 (Vanderbei, p. 328). Let `A` be skew symmetric (`n ≥ 2`), `x > 0`, `z > 0`,
`0 ≤ δ ≤ 1`, let `(Δx, Δz)` solve (22.5)–(22.6) at `(x, z)`, and let
`p = X^{-1/2}Z^{1/2}Δx`, `q = X^{1/2}Z^{-1/2}Δz`, `r = p + q` (22.11). Then
(1) `‖PQe‖ ≤ ½‖r‖²`;
(2) if `δ = 0`, then `‖r‖² = nμ`;
(3) if `δ = 1` and `(x, z) ∈ N(β)` (with `0 ≤ β < 1`), then `‖r‖² ≤ β²μ/(1 - β)`.
All norms are Euclidean. -/
theorem scaled_direction_bounds {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x z dx dz : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hz : ∀ j, 0 < z j)
    (hstep : IsStepDirection A δ x z dx dz) :
    euclidNorm (fun j => scaledDx x z dx j * scaledDz x z dz j) ≤
        (1 / 2) * euclidNorm (scaledDx x z dx + scaledDz x z dz) ^ 2 ∧
    (δ = 0 → euclidNorm (scaledDx x z dx + scaledDz x z dz) ^ 2 = (n : ℝ) * mu x z) ∧
    (δ = 1 → ∀ β : ℝ, 0 ≤ β → β < 1 → (x, z) ∈ Nbhd β →
      euclidNorm (scaledDx x z dx + scaledDz x z dz) ^ 2 ≤ β ^ 2 * mu x z / (1 - β)) := by sorry

end VanderbeiLP.SelfDual
