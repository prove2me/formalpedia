-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_eqHS_iff_eqMeas
-- name    : ProjectiveMeasurementEquilibration.eqHS_iff_eqMeas
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T15:21:35.580815+00:00
-- url     : https://prove2.me/theorems/d70f1971-fab6-4914-85ab-ae81e706a9e5
-- title:
--   Theorem 1 (part) — EQ-HS $\Leftrightarrow$ EQ-MEAS
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For every map $\Phi$ on matrices, condition EQ-HS (for every density matrix $\rho$, $\Phi(\rho)$ is a density matrix commuting with $X$ minimizing $\|\rho-\sigma\|_{HS}^2$ among density matrices $\sigma$ commuting with $X$) holds if and only if condition EQ-MEAS ($\Phi(\rho)=\sum_xP_x\rho P_x$ for every density matrix $\rho$) holds. In particular $\mathcal P_X(\rho)$ is the unique such minimizer.
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, Theorem 1 and its proof (EQ-HS ⇔ EQ-MEAS), pp. 2–3

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem eqHS_iff_eqMeas {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (Φ : Matrix n n ℂ → Matrix n n ℂ) :
    EqHS X Φ ↔ EqMeas hX Φ := by sorry

end ProjectiveMeasurementEquilibration
