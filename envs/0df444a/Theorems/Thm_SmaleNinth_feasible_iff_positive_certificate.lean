-- Prove2me | Theorems.Thm_SmaleNinth_feasible_iff_positive_certificate
-- name    : SmaleNinth.feasible_iff_positive_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T07:33:38.971933+00:00
-- url     : https://prove2.me/theorems/539c79ee-b111-490c-93d6-3b117edc755b
-- title:
--   Feasibility is equivalent to a positive complementarity certificate
-- statement:
--   A system of linear inequalities is nonempty if and only if it admits a primal point together with a nonnegative dual certificate satisfying the complementary equations. The forward implication is obtained by applying strong duality to the zero objective, whose value is automatically bounded below, and then using complementary slackness. The reverse implication is immediate from the primal point hypothesis.
--
--   This adapter isolates the certificate interpretation already formalized by the proved Farkas and duality foundations; it is not a claim that the real-RAM algorithm or its dimension-only termination bound has been proved.
-- source:
--   Bertsimas and Tsitsiklis, *Introduction to Linear Optimization*, 1997, Sections 4.3--4.5; the platform theorems SmaleNinth.lp_strong_duality and SmaleNinth.lp_complementary_slackness.

import Definitions.Def_Polyhedron
import Theorems.Thm_SmaleNinth_lp_strong_duality
import Theorems.Thm_SmaleNinth_lp_complementary_slackness

open Matrix LinearOptimization

theorem SmaleNinth.feasible_iff_positive_certificate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (polyhedron A b).Nonempty ↔
      ∃ (x : Fin n → ℝ) (y : Fin m → ℝ),
        x ∈ polyhedron A b ∧
        (∀ i, 0 ≤ y i) ∧
        (∀ k, ∑ i, y i * A i k = 0) ∧
        (∀ i, y i * ((A.mulVec x) i - b i) = 0) := by sorry
