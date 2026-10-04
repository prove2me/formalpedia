-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_pinching_isDensityMatrix
-- name    : ProjectiveMeasurementEquilibration.pinching_isDensityMatrix
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:25:09.568093+00:00
-- url     : https://prove2.me/theorems/939e2050-8b2c-4c39-9052-e6016e8395a7
-- title:
--   Proof of Theorem 1 — $\mathcal P_X$ maps density matrices to density matrices
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. If $\rho$ is a density matrix then so is $\mathcal P_X(\rho)=\sum_xP_x\rho P_x$ (the pinching is positive and trace preserving).
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1 (EQ-HS ⇔ EQ-MEAS), p. 3

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem pinching_isDensityMatrix {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (pinching hX ρ) := by sorry

end ProjectiveMeasurementEquilibration
