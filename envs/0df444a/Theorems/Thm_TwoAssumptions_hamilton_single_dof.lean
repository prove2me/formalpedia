-- Prove2me | Theorems.Thm_TwoAssumptions_hamilton_single_dof
-- name    : TwoAssumptions.hamilton_single_dof
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T23:25:52.663473+00:00
-- url     : https://prove2.me/theorems/d940c3b0-07ac-41a3-b6bf-718097f0e743
-- title:
--   §3 — Hamilton's equations for a single degree of freedom
-- statement:
--   **Hamilton's equations, single degree of freedom (§3).** A deterministic and reversible evolution of a one-degree-of-freedom system obeys
--   $$\frac{dq}{dt}=\frac{\partial H}{\partial p},\qquad \frac{dp}{dt}=-\frac{\partial H}{\partial q}.$$
--
--   Conservation of the density forces the evolution vector field $S=(dq/dt,dp/dt)$ to be divergence-free, $\partial_q S^q+\partial_p S^p=0$. A divergence-free $C^1$ planar field is the curl of a potential, and choosing the gauge $\theta=(p,0,-H)$ yields Hamilton's equations with $H$ the Hamiltonian.
--
--   **Formalization Note.** This is the stream-function theorem on $\mathbb R^2$: a divergence-free $C^1$ planar field $(u,v)$ admits a potential $H$ with $\partial_p H=u$, $\partial_q H=-v$. It is the clean mathematical core of the derivation and the key step toward the general goal. Partial derivatives are `fderiv ℝ · 1`.
-- source:
--   Cosper 2022, From Two Assumptions to Hamilton's Mechanics, https://github.com/assumptionsofphysics/thesis-ClassicalMechanics, §3, single-degree-of-freedom Hamilton equations (unnumbered display before Proposition (14)).

import Mathlib
open scoped ContDiff

namespace TwoAssumptions

theorem hamilton_single_dof (u v : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 1 (fun z : ℝ × ℝ => u z.1 z.2))
    (hv : ContDiff ℝ 1 (fun z : ℝ × ℝ => v z.1 z.2))
    (hdiv : ∀ q p, fderiv ℝ (fun q' => u q' p) q 1 + fderiv ℝ (fun p' => v q p') p 1 = 0) :
    ∃ H : ℝ → ℝ → ℝ,
      (∀ q p, fderiv ℝ (fun p' => H q p') p 1 = u q p) ∧
      (∀ q p, fderiv ℝ (fun q' => H q' p) q 1 = -v q p) := by sorry

end TwoAssumptions
