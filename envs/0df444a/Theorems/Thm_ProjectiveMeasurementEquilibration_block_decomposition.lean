-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_block_decomposition
-- name    : ProjectiveMeasurementEquilibration.block_decomposition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T10:06:21.494307+00:00
-- url     : https://prove2.me/theorems/cb06af7c-6f99-4491-9e0a-eedb30ea975c
-- title:
--   Eq. (2) — block decomposition $\rho=\sum_{x,y}P_x\rho P_y$
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For every $n\times n$ complex matrix $\rho$,$$\rho=\sum_{x,y}P_x\,\rho\,P_y,$$the double sum running over pairs of distinct eigenvalues of $X$ (block-matrix decomposition of $\rho$ with respect to the eigenspaces of $X$).
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1, eq. (2), p. 2

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem block_decomposition {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (ρ : Matrix n n ℂ) :
    ∑ x ∈ eigenvalueSet hX, ∑ y ∈ eigenvalueSet hX, eigenproj hX x * ρ * eigenproj hX y = ρ := by sorry

end ProjectiveMeasurementEquilibration
