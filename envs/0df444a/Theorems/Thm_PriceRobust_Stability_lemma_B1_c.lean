-- Prove2me | Theorems.Thm_PriceRobust_Stability_lemma_B1_c
-- name    : PriceRobust.Stability.lemma_B1_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:08.877595+00:00
-- url     : https://prove2.me/theorems/783c6123-1b8a-4726-a307-6057db9934c1
-- title:
--   Lemma B.1(c), Appendix p. 6 — AB⁻¹ and B⁻¹A are ZP-matrices when A is ZP, B is Z and A ≤ B
-- statement:
--   Let $A$ be a ZP-matrix and $B$ a Z-matrix with $A\le B$ entrywise. Then
--   $$AB^{-1}\quad\text{and}\quad B^{-1}A$$
--   are ZP-matrices.
--
--   In the proof of Theorem 3 this is applied with $A=R$ and $B=T(R)$ to show that $[T(R)]^{-1}R=I-\Lambda(R)$ is a ZP-matrix.
--
--   **Formalization Note** $B^{-1}$ is Mathlib's matrix inverse; $B$ is invertible under the hypotheses (Lemma B.1(b)).
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), Online Appendix p. 6 (PDF 26), Lemma B.1(c)

import Mathlib
import Definitions.Def_PriceRobust_Stability_ZPMatrix

open Matrix

namespace PriceRobust.Stability

theorem lemma_B1_c {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : IsZPMatrix A) (hB : IsZMatrix B) (hAB : ∀ l m, A l m ≤ B l m) :
    IsZPMatrix (A * B⁻¹) ∧ IsZPMatrix (B⁻¹ * A) := by sorry

end PriceRobust.Stability
