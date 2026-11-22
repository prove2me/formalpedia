-- Prove2me | Theorems.Thm_TwoAssumptions_prop14_hamilton
-- name    : TwoAssumptions.prop14_hamilton
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T23:26:56.351415+00:00
-- url     : https://prove2.me/theorems/6e62a824-e612-4e10-b8a8-42d04577b73e
-- title:
--   Proposition 14 (goal) — Hamilton's equations from deterministic and reversible evolution
-- statement:
--   **Proposition 14 (goal).** The deterministic and reversible evolution of an infinitesimally reducible system follows Hamilton's equations: there is a single Hamiltonian $H(q,p,t)$ with
--   $$\frac{dq^i}{dt}=\frac{\partial H}{\partial p_i},\qquad \frac{dp_i}{dt}=-\frac{\partial H}{\partial q^i}\qquad(i=1,\dots,n).$$
--
--   Assumption I gives canonical coordinates $(q^i,p_i)$ on the $2n$-dimensional particle state space, organized in independent degrees of freedom. Assumption II (deterministic and reversible evolution) conserves the density of states. The source's generalization argues that each infinitesimal degree-of-freedom surface is mapped to a surface of the same area and that independent degrees of freedom remain independent, so the evolution is autonomous and area-preserving on each conjugate pair; applying the single-degree-of-freedom result per pair and summing gives one Hamiltonian.
--
--   **Formalization Note.** The evolution is encoded per degree of freedom as a $C^1$ planar field $(u_i,v_i)(q^i,p_i,t)$ (autonomy: it depends only on the $i$-th pair and time), with the divergence-free condition $\partial_q u_i+\partial_p v_i=0$ encoding density conservation on each degree-of-freedom surface (Liouville). The conclusion asserts a single $H$ with $\partial H/\partial p_i=u_i$ and $\partial H/\partial q^i=-v_i$. The per-degree-of-freedom autonomy is the source's generalization premise, made explicit; the density-conservation-to-divergence-free step is the Liouville equivalence. This encoding choice is flagged for careful audit.
-- source:
--   Cosper 2022, From Two Assumptions to Hamilton's Mechanics, https://github.com/assumptionsofphysics/thesis-ClassicalMechanics, Proposition (14), §3 (goal theorem).

import Mathlib
open scoped ContDiff

namespace TwoAssumptions

theorem prop14_hamilton (n : ℕ)
    (u v : Fin n → ℝ → ℝ → ℝ → ℝ)
    (hu : ∀ i, ContDiff ℝ 1 (fun z : ℝ × ℝ × ℝ => u i z.1 z.2.1 z.2.2))
    (hv : ∀ i, ContDiff ℝ 1 (fun z : ℝ × ℝ × ℝ => v i z.1 z.2.1 z.2.2))
    (hdiv : ∀ i q p t, fderiv ℝ (fun q' => u i q' p t) q 1 + fderiv ℝ (fun p' => v i q p' t) p 1 = 0) :
    ∃ H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ,
      (∀ i q p t, fderiv ℝ (fun p' => H q p' t) p (Pi.single i 1) = u i (q i) (p i) t) ∧
      (∀ i q p t, fderiv ℝ (fun q' => H q' p t) q (Pi.single i 1) = -v i (q i) (p i) t) := by sorry

end TwoAssumptions
