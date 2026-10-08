-- Prove2me | Theorems.Thm_ProxAltMin_Conv_eq25
-- name    : ProxAltMin.Conv.eq25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:01.239561+00:00
-- url     : https://prove2.me/theorems/25960aaf-95a3-485f-929a-1b0b17c5f406
-- title:
--   Proof of Theorem 8, (25) — ‖zᵢ − zᵢ₋₁‖ + M(φ(lᵢ) − φ(lᵢ₊₁)) ≥ 2‖zᵢ₊₁ − zᵢ‖ inside B(z̄, ρ)
-- statement:
--   Let $L=f+Q+g$ satisfy (H) and (H1) with step sizes in $(r_-,r_+)$, let $z_k=(x_k,y_k)$ comply with (5)–(6), $l_k=L(z_k)$, and let $\bar z$ be a point with $\bar l=L(\bar z)$. Let $\eta>0$, $U\subset\mathbb R^n\times\mathbb R^m$ and $\varphi:[0,\eta)\to\mathbb R_+$ (continuous, concave, $\varphi(0)=0$, $C^1$ on $(0,\eta)$ with $\varphi'>0$) be such that the Kurdyka–Łojasiewicz inequality
--   $$\varphi'(L(z)-\bar l)\,\operatorname{dist}(0,\partial L(z))\ge1$$
--   holds for all $z\in U$ with $\bar l<L(z)<\bar l+\eta$. Let $\rho>0$ with $B(\bar z,\rho)\subset U$, let $C$ be a Lipschitz constant for $\nabla Q$ on $B(\bar z,\sqrt2\rho)$, $M=2r_+(C+1/r_-)$, and assume (15): $\bar l<l_k<\bar l+\eta$ for all $k$. If $i\ge1$ and $z_{i-1},z_i\in B(\bar z,\rho)$, then
--   $$\|z_i-z_{i-1}\|+M\big(\varphi(l_i-\bar l)-\varphi(l_{i+1}-\bar l)\big)\ge2\|z_{i+1}-z_i\|.\tag{25}$$
--
--   Summing (25) over $i$ is what yields the finite length of the sequence.
--
--   **Formalization Note** The proof normalizes $\bar l=0$; here $l_i-\bar l$ replaces the normalized $l_i$. The inequality "$\varphi'\cdot\operatorname{dist}(0,\partial L(z))\ge1$" is stated for every $v\in\partial L(z)$, the convention $\operatorname{dist}(0,\emptyset)=+\infty$.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 10, §3.3, proof of Theorem 8, (25)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
open Filter Topology

namespace ProxAltMin.Conv

/-- Proof of Theorem 8, (25) (p. 10), with `lᵢ - l̄` in place of the normalized `lᵢ`: in the setting of
Theorem 8 up to (15) (KL data `η, U, φ` of `L` at `z̄`, `B(z̄, ρ) ⊂ U`, a Lipschitz constant `C` of
`∇Q` on `B(z̄, √2 ρ)`, `M = 2r₊(C + 1/r₋)`), if `i ≥ 1` and `z_{i-1}, zᵢ ∈ B(z̄, ρ)`, then
`‖zᵢ - z_{i-1}‖ + M (φ(lᵢ - l̄) - φ(l_{i+1} - l̄)) ≥ 2 ‖z_{i+1} - zᵢ‖`. -/
theorem eq25 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu (y 0) rm rp)
    (hrun : IsPAMRun f Q g lam mu x y)
    (zbar : Z n m) (η : ℝ) (hη : 0 < η) (U : Set (Z n m)) (φ : ℝ → ℝ)
    (hφ : IsDesingularizer η φ) (hKL : KLIneq (L f Q g) zbar η U φ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρU : Metric.ball zbar ρ ⊆ U) (C : NNReal)
    (hC : LipschitzOnWith C (gradient Q) (Metric.ball zbar (Real.sqrt 2 * ρ)))
    (h15 : ∀ k : ℕ, L f Q g zbar < L f Q g (pt (x k) (y k)) ∧
      L f Q g (pt (x k) (y k)) < L f Q g zbar + (η : EReal))
    (i : ℕ) (hi : 1 ≤ i)
    (hzi : pt (x i) (y i) ∈ Metric.ball zbar ρ)
    (hzi' : pt (x (i - 1)) (y (i - 1)) ∈ Metric.ball zbar ρ) :
    ‖pt (x i) (y i) - pt (x (i - 1)) (y (i - 1))‖ +
        2 * rp * ((C : ℝ) + 1 / rm) *
          (φ (L f Q g (pt (x i) (y i)) - L f Q g zbar).toReal -
            φ (L f Q g (pt (x (i + 1)) (y (i + 1))) - L f Q g zbar).toReal) ≥
      2 * ‖pt (x (i + 1)) (y (i + 1)) - pt (x i) (y i)‖ := by sorry

end ProxAltMin.Conv
