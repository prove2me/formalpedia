-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_projective_measurement_equilibration
-- name    : ProjectiveMeasurementEquilibration.projective_measurement_equilibration
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T19:34:38.306824+00:00
-- url     : https://prove2.me/theorems/ba925f9a-388e-4053-933d-5e81546e4bfb
-- title:
--   Theorem 1 — EQ-MEAS, EQ-LIND, EQ-HS, EQ-KL are equivalent (finite dimension)
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. Let $\Phi$ be any map on matrices (the black-box spectral equilibration process $\Phi_X$; only its values on density matrices matter). Then the conditions
--
--   - **EQ-MEAS**: $\Phi(\rho)=\sum_xP_x\rho P_x$;
--   - **EQ-LIND**: $\Phi(\rho)=\lim_{t\to\infty}\rho(t)$, where $\frac{d\rho}{dt}=X\rho X-\tfrac12\{X^2,\rho\}$, $\rho(0)=\rho$;
--   - **EQ-HS**: $\Phi(\rho)=\operatorname{argmin}_{\sigma\in D,\,[\sigma,X]=0}\|\rho-\sigma\|_{HS}^2$;
--   - **EQ-KL**: $\Phi(\rho)=\operatorname{argmin}_{\sigma\in D,\,[\sigma,X]=0}D(\rho\|\sigma)$,
--
--   each required for all density matrices $\rho$, are pairwise equivalent. This is Theorem 1 of the source specialised to finite-dimensional Hilbert spaces, where Condition [B]FINENT holds automatically.
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, Theorem 1, p. 2 (proof pp. 2–4)

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem projective_measurement_equilibration {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (Φ : Matrix n n ℂ → Matrix n n ℂ) :
    (EqMeas hX Φ ↔ EqLind X Φ) ∧ (EqMeas hX Φ ↔ EqHS X Φ) ∧ (EqMeas hX Φ ↔ EqKL X Φ) := by sorry

end ProjectiveMeasurementEquilibration
