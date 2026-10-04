-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_commute_iff_pinching_eq
-- name    : ProjectiveMeasurementEquilibration.commute_iff_pinching_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T13:46:16.589933+00:00
-- url     : https://prove2.me/theorems/38964c1f-060a-4e9a-a006-acf15eacaf0e
-- title:
--   Proof of Theorem 1 — $[\sigma,X]=0\iff\mathcal P_X(\sigma)=\sigma$
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For every $n\times n$ complex matrix $\sigma$: $\sigma$ commutes with $X$ if and only if $\sigma$ is block diagonal with respect to the eigenspaces of $X$, i.e. $$[\sigma,X]=0\iff \mathcal P_X(\sigma)=\sum_xP_x\sigma P_x=\sigma.$$
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1 (EQ-HS ⇔ EQ-MEAS, first paragraph), p. 3

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem commute_iff_pinching_eq {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (σ : Matrix n n ℂ) :
    X * σ = σ * X ↔ pinching hX σ = σ := by sorry

end ProjectiveMeasurementEquilibration
