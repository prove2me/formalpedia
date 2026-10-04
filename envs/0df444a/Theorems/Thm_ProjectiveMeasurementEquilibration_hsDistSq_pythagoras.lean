-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_hsDistSq_pythagoras
-- name    : ProjectiveMeasurementEquilibration.hsDistSq_pythagoras
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:46:29.768492+00:00
-- url     : https://prove2.me/theorems/08dedc92-db7f-401a-b044-e77f4d9dc55d
-- title:
--   Eq. (11) — Pythagorean identity for the Hilbert–Schmidt distance
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For all $n\times n$ complex matrices $\rho,\sigma$ with $[\sigma,X]=0$, $$\|\rho-\sigma\|_{HS}^2=\|\rho-\mathcal P_X(\rho)\|_{HS}^2+\|\mathcal P_X(\rho)-\sigma\|_{HS}^2.$$
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1, eq. (11), p. 3

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem hsDistSq_pythagoras {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (ρ σ : Matrix n n ℂ) (hσ : X * σ = σ * X) :
    hsDistSq ρ σ = hsDistSq ρ (pinching hX ρ) + hsDistSq (pinching hX ρ) σ := by sorry

end ProjectiveMeasurementEquilibration
