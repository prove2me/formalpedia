-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_swap_one_step_delay
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.swap_one_step_delay
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:36:57.986444+00:00
-- url     : https://prove2.me/theorems/7bda044f-e55d-4bd8-833c-8cebc667cafe
-- title:
--   Repeated SWAP delays each qubit input by one use
-- statement:
--   Consider a qubit system and a qubit memory initially in a density matrix $\xi$. Apply SWAP between memory and each successive independent qubit input $\rho_j$, retaining the resulting memory without reset. With one-based use indices,
--
--   $$\rho^{\rm out}_1=\xi,\qquad \rho^{\rm out}_j=\rho_{j-1}\quad(j\ge2).$$
--
--   For a first block of $N\ge1$ identical density inputs $\rho$, the exact mean output is
--
--   $$\frac1N\sum_{j=1}^N\rho^{\rm out}_j=\frac1N\xi+\frac{N-1}{N}\rho.$$
--
--   This identifies the first-use boundary and the one-step delay underlying the source's tomography example.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 3, Section II.A, equation (2.4) and first-block average

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section II.A, PDF pp.2–3, (2.4): qubit SWAP outputs the initializer first and
then the preceding input. Includes the exact first-block average, for N>0. -/
theorem swap_one_step_delay (D : MemoryDevice 2 2)
    (hSwap : (D.unitary : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      (swapOp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) :
    (∀ input : ℕ → Operator 2, (∀ j, IsDensityMatrix (input j)) →
      outputState D input 0 = D.initial ∧
        ∀ j, outputState D input (j + 1) = input j) ∧
    (∀ rho : Operator 2, IsDensityMatrix rho → ∀ N : ℕ, 0 < N →
      firstBlockMean D rho N = ((N : ℂ)⁻¹) • D.initial +
        (((N - 1 : ℕ) : ℂ) / (N : ℂ)) • rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
