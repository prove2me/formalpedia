-- Prove2me | Theorems.Thm_PeresTerno_transpose_not_completelyPositive
-- name    : PeresTerno.transpose_not_completelyPositive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T09:21:29.745976+00:00
-- url     : https://prove2.me/theorems/1ad1af60-d195-4395-8d15-51b30f881f16
-- title:
--   Time reversal ($\rho\mapsto\rho^T$) is not completely positive
-- statement:
--   The transposition map $\rho\mapsto\rho^{T}$ on complex $2\times 2$ matrices is **not** completely positive: there are $n\in\mathbb N$ and a positive semidefinite matrix $R$ on $\mathbb C^2\otimes\mathbb C^n$ such that applying the transposition to each $2\times 2$ block of $R$ (the partial transpose) yields a matrix that is not positive semidefinite.
--
--   This is the source's remark that time reversal applied to only one of two systems produces an unphysical "density matrix" with negative eigenvalues.
--
--   **Formalization Note** Stated for a qubit; this suffices to show that time reversal is not completely positive in general.
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, p. 100, Sec. II.D, "However, it is not completely positive"

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem transpose_not_completelyPositive :
    ¬ IsCompletelyPositive (fun ρ : Matrix (Fin 2) (Fin 2) ℂ => ρᵀ) := by
  sorry

end PeresTerno
