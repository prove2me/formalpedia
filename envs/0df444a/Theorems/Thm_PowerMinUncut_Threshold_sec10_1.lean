-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_sec10_1
-- name    : PowerMinUncut.Threshold.sec10_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:17.360193+00:00
-- url     : https://prove2.me/theorems/5a13c35d-bb72-47f8-846d-366c1f8dbc43
-- title:
--   §10.1 — sequential mixed-sign endpoint for ball maps with vanishing norm deficit
-- statement:
--   Let $q\ge2$ be an integer and $a_\rho=[2(1-\rho)]^{q/2}$. Let $\rho_n\uparrow1$, let $J_n$ be diagonal matrices with entries in $\{-1,1\}$ on $\mathbb R^{N_n}$, and let $h_n:\mathbb R^{N_n}\to B^k$ be measurable maps with
--   $$1-\|h_n\|_2^2\to0,\qquad \|h\|_2^2=\mathbb E\|h(X)\|^2 .$$
--   Write $e_n=\mathbb E_{\rho_nJ_n}\|h_n(X)+h_n(Y)\|^q/a_{\rho_n}$, where $\mathbb E_C$ means that $X,Y$ have standard Gaussian marginals and cross-covariance $C$. If $k>q$ and $\sup_ne_n<\infty$, then
--   $$\liminf_{n\to\infty}e_n\ \ge\ C_{k,q}.$$
--   For $2\le k\le q$ no such bounded normalized-energy sequence exists. The statement is uniform in $N_n$ and in the multiplicities of both signs.
--
--   Differences from the source:
--   - encoding: liminf e_n ≥ C_{k,q} → for every ε > 0, eventually e_n ≥ C_{k,q} − ε; reason: equivalent for a sequence bounded above
--   - encoding: no such bounded normalized-energy sequence exists → under the other hypotheses, the sequence (e_n) is not bounded above; reason: the same statement
--   - encoding: ρ_n ↑ 1 → Monotone ρ, ρ_n < 1, ρ_n → 1, and −1 ≤ ρ_n; reason: −1 ≤ ρ_n only excludes cross-covariances ρ_nJ_n that no Gaussian pair has
--   - encoding: E_{ρJ} → Y_i = ρJ_iX_i + √(1 − ρ²) Z_i with Z independent of X; reason: a realization of the Gaussian pair with cross-covariance ρJ
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 50, §10.1

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Instance
import Definitions.Def_PowerMinUncut_Threshold_Gaussian

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **§10.1, sequential mixed-sign endpoint**, p. 50. Let `q ≥ 2`, `ρ_n ↑ 1`, `J_n` diagonal sign
matrices on `ℝ^{N_n}`, and `h_n : ℝ^{N_n} → B^k` measurable with `1 - ‖h_n‖_2² → 0`
(`‖h‖_2² = E‖h(X)‖²`). Write `e_n = E_{ρ_n J_n}‖h_n(X) + h_n(Y)‖^q / a_{ρ_n}`. If `k > q` and
`sup_n e_n < ∞` then `liminf e_n ≥ C_{k,q}` (for every `ε > 0` eventually `e_n ≥ C_{k,q} - ε`); if
`2 ≤ k ≤ q`, `sup_n e_n = ∞`. -/
theorem sec10_1 (q k : ℕ) (hq : 2 ≤ q) (ρ : ℕ → ℝ) (hρmono : Monotone ρ)
    (hρlo : ∀ n, -1 ≤ ρ n) (hρlt : ∀ n, ρ n < 1) (hρlim : Tendsto ρ atTop (𝓝 1))
    (N : ℕ → ℕ) (J : ∀ n, Fin (N n) → ℝ) (hJ : ∀ n i, J n i = 1 ∨ J n i = -1)
    (h : ∀ n, E (N n) → E k) (hmeas : ∀ n, Measurable (h n)) (hball : ∀ n x, ‖h n x‖ ≤ 1)
    (hdef : Tendsto (fun n => 1 - ∫ x, ‖h n x‖ ^ 2 ∂stdGaussian (E (N n))) atTop (𝓝 0)) :
    (q < k →
      BddAbove (Set.range fun n =>
        pairExp (fun i => ρ n * J n i) (fun x y => ‖h n x + h n y‖ ^ q) / aRho q (ρ n)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        Ckp k q - ε ≤
          pairExp (fun i => ρ n * J n i) (fun x y => ‖h n x + h n y‖ ^ q) / aRho q (ρ n)) ∧
    (2 ≤ k → k ≤ q →
      ¬ BddAbove (Set.range fun n =>
        pairExp (fun i => ρ n * J n i) (fun x y => ‖h n x + h n y‖ ^ q) / aRho q (ρ n))) := by sorry

end PowerMinUncut.Threshold
