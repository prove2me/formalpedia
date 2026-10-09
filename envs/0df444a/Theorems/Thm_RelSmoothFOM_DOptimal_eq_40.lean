-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_eq_40
-- name    : RelSmoothFOM.DOptimal.eq_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:48.072166+00:00
-- url     : https://prove2.me/theorems/98f11553-ffec-48f9-bf96-bc2c90357fea
-- title:
--   Equation (40) — an interior approximation to the optimum
-- statement:
--   Let $x^*$ minimize the D-optimal objective $f$ among feasible simplex points with positive-definite information matrix. Start at $x^0=e/n$, assume $0<\varepsilon\le f(x^0)-f(x^*)$, and set
--   $$\delta=\frac{\varepsilon}{2(f(x^0)-f(x^*))},\qquad \hat x=(1-\delta)x^*+\delta x^0.$$
--   Then $0<\delta\le1/2$, $\hat x$ lies in the positive simplex, and convexity gives
--   $$f(\hat x)\le(1-\delta)f(x^*)+\delta f(x^0),\qquad f(\hat x)-f(x^*)\le\delta(f(x^0)-f(x^*)).$$
--   The positive comparison point connects the boundary-capable optimum to the interior algorithm estimate.
--
--   **Formalization Note** The positive-simplex conclusion records the page's $\hat x\ge(\delta/n)e$. Positivity of $\varepsilon$ is explicit because $\delta$ divides by the initial gap.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 349, (40) and preceding proof of Theorem 4.1

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- The interior approximation and convexity bound (40). -/
theorem eq_40 {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (hmn : m + 1 ≤ n)
    (xstar : Fin n → ℝ) (hxs : xstar ∈ stdSimplex ℝ (Fin n))
    (hxspd : (H * Matrix.diagonal xstar * H.transpose).PosDef)
    (hopt : ∀ y ∈ stdSimplex ℝ (Fin n),
      (H * Matrix.diagonal y * H.transpose).PosDef →
        dOptObj H xstar ≤ dOptObj H y)
    (ε : ℝ) (hε : 0 < ε)
    (hεle : ε ≤ dOptObj H (fun _ => 1 / (n : ℝ)) - dOptObj H xstar) :
    let x0 : Fin n → ℝ := fun _ => 1 / (n : ℝ)
    let δ := ε / (2 * (dOptObj H x0 - dOptObj H xstar))
    let xhat := (1 - δ) • xstar + δ • x0
    0 < δ ∧ δ ≤ 1 / 2 ∧ xhat ∈ posSimplex n ∧
    dOptObj H xhat ≤ (1 - δ) * dOptObj H xstar + δ * dOptObj H x0 ∧
    dOptObj H xhat - dOptObj H xstar ≤
      δ * (dOptObj H x0 - dOptObj H xstar) := by sorry

end RelSmoothFOM.DOptimal
