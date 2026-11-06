-- Prove2me | Theorems.Thm_TiltedCvx_theorem_22
-- name    : TiltedCvx.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:33.18255+00:00
-- url     : https://prove2.me/theorems/beb15c2b-474b-4658-93b9-4432ad21187a
-- title:
--   Theorem 22 — $\mathcal F^\gamma\subseteq\mathcal F^{\eta(\gamma)}_{\mathrm{sec}}$ and the bounds on $\eta(\gamma)$
-- statement:
--   Let $\gamma\in(0,1]$ and let $\tau_\gamma\in(0,1/2]$ be the unique solution of
--
--   $$
--   \tau_\gamma^{\gamma}+\tau_\gamma=1,\qquad\text{and set}\qquad \eta(\gamma):=\Big(\frac{\tau_\gamma}{1-\tau_\gamma}\Big)^2 .
--   $$
--
--   Every proper lsc $\gamma$–tilted convex function belongs to $\mathcal F^{\eta(\gamma)}_{\mathrm{sec}}$. Moreover, if $\gamma\in(0,1)$, then
--
--   $$
--   \gamma^2+\frac{\gamma^3(1-\gamma)}{2}\ \le\ \eta(\gamma)\ <\ \gamma ,
--   $$
--
--   and $\eta(1)=1$.
--
--   This improves the parameter $\gamma^2$ obtained by going through tilted monotonicity.
--
--   **Formalization Note** $\tau_\gamma$ is defined as a supremum; the theorem asserts that it lies in $(0,1/2]$ and is the unique nonnegative solution of the equation.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - reading: τγ ∈ (0, 1/2] the unique solution of τγ^γ + τγ = 1 → tau γ ∈ (0, 1/2] solves it and every solution t ≥ 0 equals tau γ; reason: 'the unique solution' of an equation in a real power, whose base must be nonnegative
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 22, p.27

import Mathlib
import Definitions.Def_TiltedCvx_tau
import Definitions.Def_TiltedCvx_eta
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_classSec

namespace TiltedCvx

/-- **Theorem 22 (the sharp secant parameter of `F^γ`).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 22, p.27. Let `γ ∈ (0, 1]` and let `τγ ∈ (0, 1/2]` be the unique
solution of `τγ^γ + τγ = 1` (23). Set `η(γ) := (τγ/(1 − τγ))²`. Every proper lsc γ–tilted convex
function belongs to `F^{η(γ)}_sec`. Moreover, if `γ ∈ (0, 1)`, then
`γ² + γ³(1 − γ)/2 ≤ η(γ) < γ` (24). For `γ = 1`, `η(1) = 1`.

**Formalization Note** `tau γ` is defined as a supremum; the first conjunct states that it lies in
`(0, 1/2]` and is the unique nonnegative solution of (23). `F^γ` and `F^{η(γ)}_sec` are classes
of functions on a finite-dimensional real inner product space `E`. -/
theorem theorem_22 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (0 < tau γ ∧ tau γ ≤ 1 / 2 ∧ tau γ ^ γ + tau γ = 1 ∧
      ∀ t : ℝ, 0 ≤ t → t ^ γ + t = 1 → t = tau γ) ∧
    (classF γ : Set (E → EReal)) ⊆ classSec (eta γ) ∧
    (γ < 1 → γ ^ 2 + γ ^ 3 * (1 - γ) / 2 ≤ eta γ ∧ eta γ < γ) ∧
    eta 1 = 1 := by sorry

end TiltedCvx
