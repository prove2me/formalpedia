-- Prove2me | Theorems.Thm_TsengCGD_Global_theorem1_a
-- name    : TsengCGD.Global.theorem1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:27.846894+00:00
-- url     : https://prove2.me/theorems/bf9254ce-76dc-441b-a06b-a563b76e24b9
-- title:
--   Theorem 1(a) — monotone objective and quantitative descent
-- statement:
--   Consider a CGD run for $F_c$ under Assumption 1, with Armijo steps and initial trial steps bounded below by a positive constant. If $\underline\lambda>0$ is the uniform lower matrix bound and $\Delta^k$ is defined by (10), then every iterate remains in the effective domain, $F_c(x^k)$ is nonincreasing, and for each $k$,
--
--   $$-\Delta^k\ge(1-\gamma)(d^k)^\top H^kd^k
--   \ge(1-\gamma)\underline\lambda\|d^k\|^2,$$
--
--   $$F_c(x^{k+1})-F_c(x^k)\le\sigma\alpha^k\Delta^k\le0.$$
--
--   These are the descent estimates used in the subsequent global-convergence claims.
--
--   **Formalization Note** The CGD run uses exact minimizers, and Armijo chooses the first accepted exponent. The whole preamble of Theorem 1, including the positive lower bound on initial trial steps, is retained. Domain membership is explicit because $F_c$ is finite only on $D$.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 399, Theorem 1(a), equations (26)–(27), https://doi.org/10.1007/s10107-007-0170-0

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem theorem1_a {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar)
    (hinit : ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ αinit k) :
    let Δ := fun k => Delta f P c γ (H k) (x k) (d k)
    Antitone (fun k => Fc f P c (x k)) ∧
    (∀ k, x k ∈ D) ∧
    (∀ k, (1 - γ) * qf (H k) (d k) ≤ -Δ k ∧
      (1 - γ) * lam * ‖d k‖ ^ 2 ≤ (1 - γ) * qf (H k) (d k)) ∧
    (∀ k, Fc f P c (x (k + 1)) - Fc f P c (x k) ≤ σ * α k * Δ k ∧
      σ * α k * Δ k ≤ 0) := by sorry

end TsengCGD.Global
