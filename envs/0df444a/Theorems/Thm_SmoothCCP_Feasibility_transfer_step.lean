-- Prove2me | Theorems.Thm_SmoothCCP_Feasibility_transfer_step
-- name    : SmoothCCP.Feasibility.transfer_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:19.668262+00:00
-- url     : https://prove2.me/theorems/7d4e9424-a951-4c41-9d0b-b0d4bd8b556e
-- title:
--   Proof of Theorem 3.13, p. 14 — x ∈ X^{N,2t}_{ε,(δ−β)} and ‖x − z‖∞ ≤ t/L give F^N_ε(−t; z) ≥ 1 − δ + β
-- statement:
--   Let $\Gamma_\varepsilon$ be built from an admissible $\gamma_\varepsilon$ and fix sample values $\xi_1,\dots,\xi_N$. Let $L>0$, $t>0$, and suppose $C$ is $L$-Lipschitz in the sup norm at every drawn scenario:
--   $$|C(x,\xi_i)-C(y,\xi_i)|\le L\|x-y\|_\infty\qquad\text{for all }i\text{ and all }x,y\in X.$$
--   If $x\in X^{N,2t}_{\varepsilon,(\delta-\beta)}$, i.e. $x\in X$ and $F^N_\varepsilon(-2t;x)\ge1-\delta+\beta$, and $z\in X$ satisfies $\|x-z\|_\infty\le t/L$, then
--   $$F^N_\varepsilon(-t;z)\ge 1-\delta+\beta .$$
--
--   This is the step that transfers sample feasibility from an arbitrary point $x$ to its representative $z$ in the net, at the cost of halving the shift from $2t$ to $t$.
--
--   **Formalization Note** The paper's argument holds "w.p.1": Assumption 3.12 holds for almost every $\xi$, hence almost surely at all drawn scenarios at once. This item is the deterministic core on one realisation of the sample, with Assumption 3.12 stated at the drawn points; the passage from almost-sure Lipschitz continuity to the drawn points is part of the proof of Theorem 3.13. Monotonicity of $\Gamma_\varepsilon$ is not assumed; it follows from admissibility.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Theorem 3.13, p. 14, "Consider now any x ∈ X^{N,2t}_{ε,(δ−β)} … F^N_ε(−t; z) ≥ F^N_ε(−2t; x) ≥ 1 − δ + β w.p.1"; Assumption 3.12, p. 14

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
open MeasureTheory

namespace SmoothCCP.Feasibility

theorem transfer_step {n N : ℕ} {Ξ : Type} (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ))
    (ε : ℝ) (γ : ℝ → ℝ) (hγ : AdmissibleGamma ε γ) (ξs : Fin N → Ξ)
    (L t δ β : ℝ) (hL : 0 < L) (ht : 0 < t)
    (hLip : ∀ i, ∀ x ∈ X, ∀ y ∈ X, |C x (ξs i) - C y (ξs i)| ≤ L * ‖x - y‖)
    (x z : Fin n → ℝ) (hx : x ∈ sampleFeasible C X ε γ ξs (2 * t) (δ - β)) (hz : z ∈ X)
    (hxz : ‖x - z‖ ≤ t / L) :
    1 - δ + β ≤ sampleCdf C ε γ ξs (-t) z := by sorry

end SmoothCCP.Feasibility
