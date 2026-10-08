-- Prove2me | Theorems.Thm_ProxAltMin_Conv_eq26
-- name    : ProxAltMin.Conv.eq26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:50.042494+00:00
-- url     : https://prove2.me/theorems/704b322b-4852-43d9-bb66-c298f8884043
-- title:
--   Proof of Theorem 8, (26) — Σ_{i ≥ k} ‖zᵢ₊₁ − zᵢ‖ ≤ Mφ(lₖ) + ‖zₖ − zₖ₋₁‖ for k ≥ 1
-- statement:
--   Assume all the hypotheses of Theorem 8: $L=f+Q+g$ satisfies (H) and (H1) with step sizes in $(r_-,r_+)$; $z_k=(x_k,y_k)$ complies with (5)–(6), $l_k=L(z_k)$, $\bar l=L(\bar z)$; $\eta>0$, $U$ and the desingularizing $\varphi$ are such that the Kurdyka–Łojasiewicz inequality holds for $L$ at $\bar z$ on $U\cap[\bar l<L<\bar l+\eta]$; $\rho>0$ with $B(\bar z,\rho)\subset U$; $C$ is a Lipschitz constant for $\nabla Q$ on $B(\bar z,\sqrt2\rho)$ and $M=2r_+(C+1/r_-)$; and
--   $$\bar l<l_k<\bar l+\eta\ \ (k\ge0),\tag{15}$$
--   $$M\varphi(l_0-\bar l)+2\sqrt{2r_+}\sqrt{l_0-\bar l}+\|z_0-\bar z\|<\rho.\tag{16}$$
--   Then for every $k\ge1$ the series $\sum_{i\ge k}\|z_{i+1}-z_i\|$ converges and
--   $$\sum_{i=k}^{\infty}\|z_{i+1}-z_i\|\le M\varphi(l_k-\bar l)+\|z_k-z_{k-1}\|.\tag{26}$$
--
--   This tail estimate gives the finite length of the sequence and, from it, estimate (18) of Theorem 8.
--
--   **Formalization Note** The proof normalizes $\bar l=0$; here $l_k-\bar l$ replaces the normalized $l_k$. Convergence of the series is stated explicitly, so the bound is not about the value a library assigns to a divergent sum.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 11, §3.3, proof of Theorem 8, (26)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
open Filter Topology

namespace ProxAltMin.Conv

/-- Proof of Theorem 8, (26) (p. 11), with `lₖ - l̄` in place of the normalized `lₖ`: under all the
hypotheses of Theorem 8, including (15) and (16), with `M = 2r₊(C + 1/r₋)`, for every `k ≥ 1` the series
`∑_{i ≥ k} ‖z_{i+1} - zᵢ‖` converges and `∑_{i=k}^∞ ‖z_{i+1} - zᵢ‖ ≤ M φ(lₖ - l̄) + ‖zₖ - z_{k-1}‖`. -/
theorem eq26 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
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
    (h16 : 2 * rp * ((C : ℝ) + 1 / rm) * φ (L f Q g (pt (x 0) (y 0)) - L f Q g zbar).toReal +
        2 * Real.sqrt (2 * rp) * Real.sqrt (L f Q g (pt (x 0) (y 0)) - L f Q g zbar).toReal +
        ‖pt (x 0) (y 0) - zbar‖ < ρ) :
    ∀ k : ℕ, 1 ≤ k →
      Summable (fun i => ‖pt (x (k + i + 1)) (y (k + i + 1)) - pt (x (k + i)) (y (k + i))‖) ∧
      ∑' i, ‖pt (x (k + i + 1)) (y (k + i + 1)) - pt (x (k + i)) (y (k + i))‖ ≤
        2 * rp * ((C : ℝ) + 1 / rm) * φ (L f Q g (pt (x k) (y k)) - L f Q g zbar).toReal +
          ‖pt (x k) (y k) - pt (x (k - 1)) (y (k - 1))‖ := by sorry

end ProxAltMin.Conv
