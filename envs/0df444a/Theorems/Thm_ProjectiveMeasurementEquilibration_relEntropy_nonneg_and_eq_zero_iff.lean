-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_relEntropy_nonneg_and_eq_zero_iff
-- name    : ProjectiveMeasurementEquilibration.relEntropy_nonneg_and_eq_zero_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T17:14:41.303411+00:00
-- url     : https://prove2.me/theorems/de269115-7fec-4a12-9e9a-02964b98367f
-- title:
--   Proof of Theorem 1 — $D(\rho\|\sigma)\ge0$ with equality iff $\rho=\sigma$
-- statement:
--   For density matrices $\rho,\sigma$ on $\mathbb C^n$ ($n$ finite), the relative entropy $D(\rho\|\sigma)\in(-\infty,+\infty]$ is non-negative, and $D(\rho\|\sigma)=0$ if and only if $\rho=\sigma$ (Klein's inequality with its equality case). This is the fact used in the source when it says that the last term of (12) \"is non-negative and vanishes if and only if $\sigma=P_X(\rho)$\".
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1 (EQ-KL ⇔ EQ-MEAS, last paragraph), p. 4

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem relEntropy_nonneg_and_eq_zero_iff {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    0 ≤ relEntropy ρ σ ∧ (relEntropy ρ σ = 0 ↔ ρ = σ) := by sorry

end ProjectiveMeasurementEquilibration
