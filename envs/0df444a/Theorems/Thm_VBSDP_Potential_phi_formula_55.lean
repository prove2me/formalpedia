-- Prove2me | Theorems.Thm_VBSDP_Potential_phi_formula_55
-- name    : VBSDP.Potential.phi_formula_55
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:26:04.663987+00:00
-- url     : https://prove2.me/theorems/93bbbaff-e058-4290-b49e-ecac96732949
-- title:
--   (55) — expanded determinant formula for the potential
-- statement:
--   Let $(x,Z)$ be a strictly feasible pair for the semidefinite program with symmetric matrices $F_0,\ldots,F_m$, linearly independent $F_1,\ldots,F_m$, matrix size $n\ge1$, and $\nu\ge1$. The potential also has the form
--
--   $$\varphi(x,Z)=(n+\nu\sqrt n)\log\operatorname{Tr}(F(x)Z)-\log\det F(x)-\log\det Z-n\log n.$$
--
--   This is the second equality of (55), separating the primal and dual determinant terms.
--
--   **Formalization Note** Strict feasibility ensures the determinants and trace are positive. Linear independence is retained from the standing assumption of §4. $F_0$ is separate from the zero-based `Fin m` family.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 76 (PDF p. 28), (55), with §4 assumptions on p. 70, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Potential_IsStrictlyFeasiblePair
import Definitions.Def_VBSDP_Potential_phi

namespace VBSDP.Potential

/-- The second line of (55), splitting the determinant of F(x)Z. -/
theorem phi_formula_55 {m n : ℕ} [NeZero n] (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (h : IsStrictlyFeasiblePair c F₀ F x Z) :
    phi ν F₀ F x Z =
      (n + ν * Real.sqrt n) * Real.log (VBSDP.Duality.lmi F₀ F x * Z).trace -
      Real.log (VBSDP.Duality.lmi F₀ F x).det - Real.log Z.det - n * Real.log n := by sorry

end VBSDP.Potential
