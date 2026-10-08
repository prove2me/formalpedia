-- Prove2me | Theorems.Thm_ProxAltMin_Conv_eq19_eq20
-- name    : ProxAltMin.Conv.eq19_eq20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:53.777082+00:00
-- url     : https://prove2.me/theorems/5ef09d00-0ec3-4171-a902-9c6c62d62db0
-- title:
--   Proof of Theorem 8, (19)–(20) — lᵢ − lᵢ₊₁ ≥ ‖zᵢ₊₁ − zᵢ‖²/(2r₊) and φ(lᵢ) − φ(lᵢ₊₁) ≥ φ′(lᵢ)‖zᵢ₊₁ − zᵢ‖²/(2r₊)
-- statement:
--   Let $L=f+Q+g$ satisfy (H) and (H1) with step sizes in $(r_-,r_+)$, let $z_k=(x_k,y_k)$ comply with (5)–(6), and write $l_k=L(z_k)$. Let $\bar z$ be a point with $\bar l=L(\bar z)$, let $\eta>0$, and let $\varphi:[0,\eta)\to\mathbb R_+$ be continuous, concave, with $\varphi(0)=0$, $C^1$ on $(0,\eta)$ and $\varphi'>0$ there. Assume (15): $\bar l<l_k<\bar l+\eta$ for all $k\ge0$. Then for every $i\ge0$
--   $$(l_i-\bar l)-(l_{i+1}-\bar l)\ge\frac1{2r_+}\|z_{i+1}-z_i\|^2,\tag{19}$$
--   $$\varphi(l_i-\bar l)-\varphi(l_{i+1}-\bar l)\ge\frac{\varphi'(l_i-\bar l)}{2r_+}\|z_{i+1}-z_i\|^2.\tag{20}$$
--
--   These are the first two estimates of the proof of Theorem 8: the decrease of $L$ is transported through the desingularizing function.
--
--   **Formalization Note** The proof normalizes $\bar l=0$; here $l_i-\bar l$ appears in place of the normalized $l_i$. Under (15) every $l_k$ and $\bar l$ is finite and $l_k-\bar l\in(0,\eta)$ is a real number.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 9, §3.3, proof of Theorem 8, (19)–(20)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
open Filter Topology

namespace ProxAltMin.Conv

/-- Proof of Theorem 8, (19)–(20) (p. 9), with `lᵢ - l̄` in place of the normalized `lᵢ`
(`lᵢ = L(zᵢ)`, `l̄ = L(z̄)`, `zᵢ = (xᵢ, yᵢ)`): for a run of (5)–(6) under (H), (H1), a desingularizing
function `φ` on `[0, η)`, and `l̄ < lₖ < l̄ + η` for all `k` (15), for every `i ≥ 0`
(19) `(lᵢ - l̄) - (l_{i+1} - l̄) ≥ ‖z_{i+1} - zᵢ‖² / (2r₊)`, and
(20) `φ(lᵢ - l̄) - φ(l_{i+1} - l̄) ≥ φ'(lᵢ - l̄) / (2r₊) · ‖z_{i+1} - zᵢ‖²`. -/
theorem eq19_eq20 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu (y 0) rm rp)
    (hrun : IsPAMRun f Q g lam mu x y)
    (zbar : Z n m) (η : ℝ) (hη : 0 < η) (φ : ℝ → ℝ) (hφ : IsDesingularizer η φ)
    (h15 : ∀ k : ℕ, L f Q g zbar < L f Q g (pt (x k) (y k)) ∧
      L f Q g (pt (x k) (y k)) < L f Q g zbar + (η : EReal)) :
    ∀ i : ℕ,
      (L f Q g (pt (x i) (y i)) - L f Q g zbar).toReal -
          (L f Q g (pt (x (i + 1)) (y (i + 1))) - L f Q g zbar).toReal ≥
        1 / (2 * rp) * ‖pt (x (i + 1)) (y (i + 1)) - pt (x i) (y i)‖ ^ 2 ∧
      φ (L f Q g (pt (x i) (y i)) - L f Q g zbar).toReal -
          φ (L f Q g (pt (x (i + 1)) (y (i + 1))) - L f Q g zbar).toReal ≥
        deriv φ (L f Q g (pt (x i) (y i)) - L f Q g zbar).toReal / (2 * rp) *
          ‖pt (x (i + 1)) (y (i + 1)) - pt (x i) (y i)‖ ^ 2 := by sorry

end ProxAltMin.Conv
