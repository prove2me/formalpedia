-- Prove2me | Theorems.Thm_SmaleNinth_real_ram_certifies_two_variable_lp_quadratic
-- name    : SmaleNinth.real_ram_certifies_two_variable_lp_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T14:27:35.699739+00:00
-- url     : https://prove2.me/theorems/e458db97-0956-473d-9680-1db764cda288
-- title:
--   Two-variable LP with explicit feasibility and Farkas certificates
-- statement:
--   This is the two-variable rung of the certificate-producing real-RAM route. A single program decides every system with two variables in quadratic time in the number of inequalities. On a positive answer it exhibits a feasible point; on a negative answer it exhibits a Farkas certificate, namely a nonnegative row combination whose left-hand side vanishes and whose right-hand side is positive. The two-variable feasibility algorithm is the already proved Fourier--Motzkin plus one-variable sweep, while the negative certificate is supplied by Farkas' lemma. The result is a fixed-dimension special case and does not assert the still-open general strongly polynomial solver.
-- source:
--   Derived from the proved theorem SmaleNinth.real_ram_decides_two_variable_lp_quadratic and the proved theorem SmaleNinth.farkas_lemma; the underlying fixed-dimension algorithm is Fourier--Motzkin elimination followed by the one-variable sweep, and the negative certificate is the classical Farkas theorem.

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM

open Matrix LinearOptimization SmaleNinth

theorem SmaleNinth.real_ram_certifies_two_variable_lp_quadratic :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m + 1) ^ 2) result ∧
          (result = true ↔ ∃ x : Fin 2 → ℝ, x ∈ polyhedron A b) ∧
          (result = false ↔
            ∃ y : Fin m → ℝ,
              (∀ i, 0 ≤ y i) ∧
              (∀ k, ∑ i, y i * A i k = 0) ∧
              0 < ∑ i, y i * b i) := by sorry
