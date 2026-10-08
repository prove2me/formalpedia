-- Prove2me | Theorems.Thm_ProxAltMin_Conv_eq24
-- name    : ProxAltMin.Conv.eq24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:49.555995+00:00
-- url     : https://prove2.me/theorems/3727d520-f752-4490-bd21-1d5bb7cf2c83
-- title:
--   Proof of Theorem 8, (24) — ‖(x*ᵢ, y*ᵢ)‖ ≤ (C + 1/r₋)‖zᵢ − zᵢ₋₁‖ when zᵢ₋₁, zᵢ ∈ B(z̄, ρ)
-- statement:
--   Let $L=f+Q+g$ satisfy (H) and (H1) with step sizes in $(r_-,r_+)$, and let $z_k=(x_k,y_k)$ comply with (5)–(6). Let $\bar z\in\mathbb R^n\times\mathbb R^m$, $\rho>0$, and let $C\ge0$ be a Lipschitz constant for $\nabla Q$ on the open ball $B(\bar z,\sqrt2\rho)$. If $i\ge1$ and $z_{i-1},z_i\in B(\bar z,\rho)$, then the vector $(x_i^*,y_i^*)$ of Lemma 5 (iii) satisfies
--   $$\|(x_i^*,y_i^*)\|\le\Big(C+\frac1{r_-}\Big)\|z_i-z_{i-1}\|.\tag{24}$$
--
--   This bounds the explicit subgradient by the length of the last step, which combined with the Kurdyka–Łojasiewicz inequality gives (25).
--
--   **Formalization Note** Balls are open; the points $(x_i,y_{i-1})$ and $z_i$ at which $\nabla Q$ is compared lie in the open ball $B(\bar z,\sqrt2\rho)$.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 10, §3.3, proof of Theorem 8, (24)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared
open Filter Topology

namespace ProxAltMin.Conv

/-- Proof of Theorem 8, (24) (p. 10): for a run of (5)–(6) under (H), (H1), a point `z̄`, `ρ > 0`, and
a Lipschitz constant `C` of `∇Q` on `B(z̄, √2 ρ)`, if `z_{i-1}, zᵢ ∈ B(z̄, ρ)` with `i ≥ 1`, then the
vector `(x*ᵢ, y*ᵢ)` of Lemma 5 (iii) satisfies `‖(x*ᵢ, y*ᵢ)‖ ≤ (C + 1/r₋) ‖zᵢ - z_{i-1}‖`. -/
theorem eq24 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu (y 0) rm rp)
    (hrun : IsPAMRun f Q g lam mu x y)
    (zbar : Z n m) (ρ : ℝ) (hρ : 0 < ρ) (C : NNReal)
    (hC : LipschitzOnWith C (gradient Q) (Metric.ball zbar (Real.sqrt 2 * ρ)))
    (i : ℕ) (hi : 1 ≤ i)
    (hzi : pt (x i) (y i) ∈ Metric.ball zbar ρ)
    (hzi' : pt (x (i - 1)) (y (i - 1)) ∈ Metric.ball zbar ρ) :
    ‖zstar Q lam mu x y i‖ ≤ ((C : ℝ) + 1 / rm) * ‖pt (x i) (y i) - pt (x (i - 1)) (y (i - 1))‖ := by sorry

end ProxAltMin.Conv
