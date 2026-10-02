-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_lindblad_block_solution
-- name    : ProjectiveMeasurementEquilibration.lindblad_block_solution
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T11:13:35.014023+00:00
-- url     : https://prove2.me/theorems/66e50776-b8b4-42cd-b892-3a82559a635f
-- title:
--   Eqs. (4)–(5) — Lindblad blocks decay as $e^{-t(x-y)^2/2}$
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. Let $\rho(t)$, $t\ge0$, be any solution of the Lindblad equation $$\frac{d\rho}{dt}=X\rho X-\tfrac12\{X^2,\rho\},\qquad \rho(0)=\rho.$$ Then for all $t\ge 0$ and all real $x,y$, $$P_x\,\rho(t)\,P_y=e^{-\frac t2(x-y)^2}\,P_x\,\rho(0)\,P_y.$$ In particular diagonal blocks are constant and off-diagonal blocks decay exponentially.
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1, eqs. (3)–(5), pp. 2–3

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem lindblad_block_solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (ρ : Matrix n n ℂ) (ρt : ℝ → Matrix n n ℂ) (hsol : IsLindbladSolution X ρ ρt)
    (t : ℝ) (ht : 0 ≤ t) (x y : ℝ) :
    eigenproj hX x * ρt t * eigenproj hX y =
      ((Real.exp (-(t / 2) * (x - y) ^ 2) : ℝ) : ℂ) • (eigenproj hX x * ρ * eigenproj hX y) := by sorry

end ProjectiveMeasurementEquilibration
