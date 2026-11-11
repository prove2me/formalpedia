-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_theorem_3
-- name    : PowerMinUncut.Threshold.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:09.514004+00:00
-- url     : https://prove2.me/theorems/68b3e927-eaea-4c59-bd68-d288eb06130f
-- title:
--   Theorem 3 — uniform Gaussian endpoint: lim_{ρ↑1} inf_n inf_f E‖f(X)+f(Y)‖^q/[2(1−ρ)]^{q/2} = C_{k,q} (k > q), = ∞ (k ≤ q); same for L_q
-- statement:
--   Let $q\ge2$ be an integer. For $k>q$,
--   $$\lim_{\rho\uparrow1}\ \inf_{n\ge k}\ \inf_{f:\mathbb R^n\to S^{k-1}}\ \frac{\mathbb E\|f(X)+f(Y)\|^q}{[2(1-\rho)]^{q/2}}=C_{k,q},\qquad \mathbb E XY^{\mathsf T}=-\rho I_n,$$
--   where $X,Y$ are standard Gaussian vectors and the maps are measurable and need not be odd. For $1\le k\le q$ the normalized infimum tends to infinity. The ball-valued kernel $L_q(a,b)=[2(1+a\cdot b)]^{q/2}$, over measurable maps into the closed unit ball, has the same endpoint.
--
--   The dimension-uniform endpoint is what lets finite graphs (§7) and the hardness reduction (§10) approximate the extremal Gaussian problem.
--
--   Differences from the source:
--   - encoding: lim_{ρ↑1}, → ∞ → Tendsto along 𝓝[<] 1 to C_{k,q}, resp. to atTop; reason: Lean representation of one-sided limits
--   - encoding: E XYᵀ = −ρ I_n → Y_i = −ρX_i + √(1 − ρ²) Z_i with Z independent of X; reason: a realization of the Gaussian pair
--   - reading: the ball-valued kernel has the same endpoint → the ball-kernel infimum has limit C_{k,q} for k > q and tends to ∞ for 1 ≤ k ≤ q; reason: §5.2 and §5.4 ("the ball kernel follows from (B1)") prove it in both regimes
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 2, Theorem 3

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Instance
import Definitions.Def_PowerMinUncut_Threshold_Gaussian

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **Theorem 3 (uniform endpoint)**, p. 2. For an integer `q ≥ 2` and `k > q`,
`lim_{ρ↑1} inf_{n ≥ k} inf_{f : ℝ^n → S^{k-1}} E‖f(X) + f(Y)‖^q / [2(1-ρ)]^{q/2} = C_{k,q}` with
`E XYᵀ = -ρ I_n`, over measurable (not necessarily odd) maps; for `1 ≤ k ≤ q` the normalized
infimum tends to infinity; the ball kernel `L_q(a,b) = [2(1 + a·b)]^{q/2}` over measurable maps into
the closed unit ball has the same endpoint. -/
theorem theorem_3 (q : ℕ) (hq : 2 ≤ q) :
    (∀ k : ℕ, q < k →
      Tendsto (sphereEndpoint k q) (𝓝[<] (1 : ℝ)) (𝓝 (Ckp k q)) ∧
        Tendsto (ballEndpoint k q) (𝓝[<] (1 : ℝ)) (𝓝 (Ckp k q))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ q →
      Tendsto (sphereEndpoint k q) (𝓝[<] (1 : ℝ)) atTop ∧
        Tendsto (ballEndpoint k q) (𝓝[<] (1 : ℝ)) atTop) := by sorry

end PowerMinUncut.Threshold
