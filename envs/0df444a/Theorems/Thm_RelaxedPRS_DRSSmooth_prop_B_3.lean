-- Prove2me | Theorems.Thm_RelaxedPRS_DRSSmooth_prop_B_3
-- name    : RelaxedPRS.DRSSmooth.prop_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:37.884547+00:00
-- url     : https://prove2.me/theorems/afe92d0c-b5fe-4638-9c8e-c85c41adb801
-- title:
--   Proposition B.3, p. 34 — summable gradient increments
-- statement:
--   Under the DRS and smoothness assumptions above, let $z^*$ be a fixed point. The squared increments of the smooth gradient are summable, and
--   $$\sum_{i=0}^{\infty}\|\nabla g(x_g^i)-\nabla g(x_g^{i+1})\|^2\le\frac{\|z^0-z^*\|^2}{\gamma^2+\beta^2}.$$
--   This controls the gradient correction in the summed objective inequality.
--
--   **Formalization Note** Summability is stated explicitly, so the infinite sum is the actual series limit.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 34, Proposition B.3 (B.10)

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

open InnerProductSpace Filter

namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition B.3, p. 34, (B.10). -/
theorem prop_B_3 (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg (fun _ => 1 / 2) z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs) :
    Summable (fun i : ℕ =>
      ‖gradient g (RelaxedPRS.StrongCvx.xg Pg (z i)) - gradient g (RelaxedPRS.StrongCvx.xg Pg (z (i + 1)))‖ ^ 2) ∧
    (∑' i : ℕ,
      ‖gradient g (RelaxedPRS.StrongCvx.xg Pg (z i)) - gradient g (RelaxedPRS.StrongCvx.xg Pg (z (i + 1)))‖ ^ 2) ≤
      1 / (γ ^ 2 + β ^ 2) * ‖z 0 - zs‖ ^ 2 := by sorry

end RelaxedPRS.DRSSmooth
