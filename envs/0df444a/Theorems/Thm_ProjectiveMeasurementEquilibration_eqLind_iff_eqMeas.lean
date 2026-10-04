-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_eqLind_iff_eqMeas
-- name    : ProjectiveMeasurementEquilibration.eqLind_iff_eqMeas
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T13:25:39.614005+00:00
-- url     : https://prove2.me/theorems/57ac3333-776e-4e10-abb5-c32217e644cf
-- title:
--   Theorem 1 (part) — EQ-LIND $\Leftrightarrow$ EQ-MEAS
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For every map $\Phi$ on matrices, condition EQ-LIND (for every density matrix $\rho$ the dephasing Lindblad evolution from $\rho$ exists and converges to $\Phi(\rho)$) holds if and only if condition EQ-MEAS ($\Phi(\rho)=\sum_xP_x\rho P_x$ for every density matrix $\rho$) holds.
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, Theorem 1 and its proof (EQ-LIND ⇔ EQ-MEAS), pp. 2–3

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem eqLind_iff_eqMeas {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (Φ : Matrix n n ℂ → Matrix n n ℂ) :
    EqLind X Φ ↔ EqMeas hX Φ := by sorry

end ProjectiveMeasurementEquilibration
