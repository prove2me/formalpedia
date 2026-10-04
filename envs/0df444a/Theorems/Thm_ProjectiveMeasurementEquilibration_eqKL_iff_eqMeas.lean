-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_eqKL_iff_eqMeas
-- name    : ProjectiveMeasurementEquilibration.eqKL_iff_eqMeas
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T18:11:48.638205+00:00
-- url     : https://prove2.me/theorems/6ead620b-6ba7-45fc-91a2-2b3ab7bbd29e
-- title:
--   Theorem 1 (part) — EQ-KL $\Leftrightarrow$ EQ-MEAS
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For every map $\Phi$ on matrices, condition EQ-KL (for every density matrix $\rho$, $\Phi(\rho)$ is a density matrix commuting with $X$ minimizing $D(\rho\|\sigma)$ among density matrices $\sigma$ commuting with $X$) holds if and only if condition EQ-MEAS holds. In finite dimension every density matrix has finite entropy, so Condition [B]FINENT is automatic.
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, Theorem 1 and its proof (EQ-KL ⇔ EQ-MEAS under [B]FINENT), pp. 3–4

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem eqKL_iff_eqMeas {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (Φ : Matrix n n ℂ → Matrix n n ℂ) :
    EqKL X Φ ↔ EqMeas hX Φ := by sorry

end ProjectiveMeasurementEquilibration
