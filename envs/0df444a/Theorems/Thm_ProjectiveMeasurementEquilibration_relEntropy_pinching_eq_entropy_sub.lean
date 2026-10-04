-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_relEntropy_pinching_eq_entropy_sub
-- name    : ProjectiveMeasurementEquilibration.relEntropy_pinching_eq_entropy_sub
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:49:36.633778+00:00
-- url     : https://prove2.me/theorems/579b3f5a-b138-43a3-87fe-b71bc453ef6d
-- title:
--   Eq. (13) — $D(\rho\|\mathcal P_X\rho)=S(\mathcal P_X\rho)-S(\rho)$
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For every density matrix $\rho$, $$D(\rho\|\mathcal P_X(\rho))=S(\mathcal P_X(\rho))-S(\rho),$$ where $S(\rho)=-\operatorname{tr}(\rho\log\rho)$ is the von Neumann entropy; in particular this relative entropy is finite.
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1, eq. (13), p. 4

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem relEntropy_pinching_eq_entropy_sub {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) :
    relEntropy ρ (pinching hX ρ) =
      ((vonNeumannEntropy (pinching hX ρ) - vonNeumannEntropy ρ : ℝ) : EReal) := by sorry

end ProjectiveMeasurementEquilibration
