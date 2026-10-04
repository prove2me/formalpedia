-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_lindblad_tendsto_pinching
-- name    : ProjectiveMeasurementEquilibration.lindblad_tendsto_pinching
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T11:51:04.810096+00:00
-- url     : https://prove2.me/theorems/274e3c19-2053-4891-8935-b89cb430f02e
-- title:
--   Eqs. (9)–(10) — Lindblad evolution converges to $\mathcal P_X(\rho)$
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For every density matrix $\rho$, the Lindblad equation $\frac{d\rho}{dt}=X\rho X-\tfrac12\{X^2,\rho\}$ with initial value $\rho$ has a solution on $t\ge 0$, and every such solution satisfies $$\lim_{t\to\infty}\rho(t)=\mathcal P_X(\rho)=\sum_xP_x\rho P_x.$$ (In finite dimension all matrix norms, including the trace norm and the Hilbert–Schmidt norm, induce the entrywise topology used here.)
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1, eqs. (6)–(10), p. 3

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem lindblad_tendsto_pinching {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) :
    (∃ ρt : ℝ → Matrix n n ℂ, IsLindbladSolution X ρ ρt) ∧
    ∀ ρt : ℝ → Matrix n n ℂ, IsLindbladSolution X ρ ρt →
      Tendsto ρt atTop (𝓝 (pinching hX ρ)) := by sorry

end ProjectiveMeasurementEquilibration
