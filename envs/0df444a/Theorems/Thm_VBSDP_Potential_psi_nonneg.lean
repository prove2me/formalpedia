-- Prove2me | Theorems.Thm_VBSDP_Potential_psi_nonneg
-- name    : VBSDP.Potential.psi_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:08.112677+00:00
-- url     : https://prove2.me/theorems/3745e606-78d7-4cda-a819-cf9e020d3892
-- title:
--   p. 76 — nonnegative deviation and its equality case
-- statement:
--   Let $(x,Z)$ be a strictly feasible pair for the semidefinite program with symmetric data, linearly independent variable matrices, and matrix size $n\ge1$. Then its deviation from centrality satisfies
--
--   $$\psi(x,Z)\ge0,\qquad \psi(x,Z)=0\ \Longrightarrow\ F(x)Z=tI\ \text{for some }t\in\mathbb R.$$
--
--   Thus vanishing deviation forces the primal and dual matrices to be inverses up to scale. The nonnegativity clause is the central inequality behind the potential bound.
--
--   **Formalization Note** The page says feasible pairs, but its logarithmic formula is meaningful as a finite real quantity on strictly feasible pairs; §4 and the algorithm use that domain. $F_0$ is separate from the zero-based `Fin m` family.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 76 (PDF p. 28), §4.5, ψ ≥ 0 statement, with §4 assumptions on p. 70, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Potential_IsStrictlyFeasiblePair
import Definitions.Def_VBSDP_Potential_psi

namespace VBSDP.Potential

/-- The nonnegativity assertion for the deviation from centrality on p. 76. -/
theorem psi_nonneg {m n : ℕ} [NeZero n] (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (h : IsStrictlyFeasiblePair c F₀ F x Z) :
    0 ≤ psi F₀ F x Z ∧
      (psi F₀ F x Z = 0 → ∃ t : ℝ, VBSDP.Duality.lmi F₀ F x * Z = t • 1) := by sorry

end VBSDP.Potential
