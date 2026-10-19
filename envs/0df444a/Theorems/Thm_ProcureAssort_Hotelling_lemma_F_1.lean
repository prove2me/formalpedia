-- Prove2me | Theorems.Thm_ProcureAssort_Hotelling_lemma_F_1
-- name    : ProcureAssort.Hotelling.lemma_F_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:51.855986+00:00
-- url     : https://prove2.me/theorems/288f5ca0-66a4-4e4d-acdf-d28df3722f43
-- title:
--   Lemma F.1, p. 41 — Mp = m is consistent iff every y with Σ_i y_i M_{i,*} = 0 has Σ_i y_i m_i = 0
-- statement:
--   Let $M$ be a real matrix with finitely many rows and columns and $m$ a real vector indexed by its rows. Then the system $Mp = m$ has a solution if and only if
--   $$\text{for every } y \text{ with } \sum_i y_i M_{i,*} = 0 \text{ we have } \sum_i y_i m_i = 0.$$
--
--   This finite-dimensional Fredholm alternative is how the proof of Theorem 4.1 verifies that the pricing system (10)–(11) is consistent.
--
--   **Formalization Note** Rows and columns are indexed by arbitrary finite types; $\sum_i y_i M_{i,*}$ is `Matrix.vecMul y M`.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Lemma F.1, p. 41

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling

theorem lemma_F_1 {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) (m : ι → ℝ) :
    (∃ p : κ → ℝ, Matrix.mulVec M p = m) ↔
      ∀ y : ι → ℝ, Matrix.vecMul y M = 0 → dotProduct y m = 0 := by sorry

end ProcureAssort.Hotelling
