-- Prove2me | Theorems.Thm_TsengCGD_Global_theorem1_b
-- name    : TsengCGD.Global.theorem1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:52.718757+00:00
-- url     : https://prove2.me/theorems/fffd4f0e-c4a8-481f-8ae9-b20aaee471e5
-- title:
--   Theorem 1(b) — vanishing direction along a convergent subsequence
-- statement:
--   Under the full preamble of Theorem 1, suppose an infinite subsequence $x^{\phi(i)}$ converges to $\bar x$, where $\phi$ is strictly increasing. Then the Armijo-weighted descent quantities vanish along the **whole** run, while the directions vanish along the selected subsequence:
--
--   $$\alpha^k\Delta^k\longrightarrow0,\qquad d^{\phi(i)}\longrightarrow0.$$
--
--   If diagonal positive-definite matrices $D^k$ have uniform positive lower and finite upper spectral bounds, their corresponding block directions $d_{D^{\phi(i)}}(x^{\phi(i)};\mathcal J^{\phi(i)})$ also tend to zero. The result connects objective decrease with the stationarity residual used by later parts of Theorem 1.
--
--   **Formalization Note** A strictly increasing $\phi:\mathbb N\to\mathbb N$ represents an infinite subsequence. The bounds on $D^k$ use quadratic forms and retain the diagonality stipulated with (14)–(16). The standing assumptions, exact run, first-trial Armijo rule, Assumption 1, and lower bound on initial trial steps are explicit.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 399, Theorem 1(b), https://doi.org/10.1007/s10107-007-0170-0

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem theorem1_b {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar)
    (hinit : ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ αinit k)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (xbar : Vec n)
    (hconv : Tendsto (x ∘ φ) atTop (𝓝 xbar)) :
    let Δ := fun k => Delta f P c γ (H k) (x k) (d k)
    Tendsto (fun k => α k * Δ k) atTop (𝓝 0) ∧
    Tendsto (d ∘ φ) atTop (𝓝 0) ∧
    ∀ (Dk : ℕ → Matrix (Fin n) (Fin n) ℝ) (del delBar : ℝ),
      0 < del → del ≤ delBar →
      (∀ k, IsPosDiag (Dk k) ∧
        ∀ z : Vec n, del * ‖z‖ ^ 2 ≤ qf (Dk k) z ∧
          qf (Dk k) z ≤ delBar * ‖z‖ ^ 2) →
      Tendsto (fun i => dH f D P c (Dk (φ i)) (x (φ i)) (J (φ i)))
        atTop (𝓝 0) := by sorry

end TsengCGD.Global
