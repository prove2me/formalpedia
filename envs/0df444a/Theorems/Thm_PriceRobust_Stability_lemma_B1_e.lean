-- Prove2me | Theorems.Thm_PriceRobust_Stability_lemma_B1_e
-- name    : PriceRobust.Stability.lemma_B1_e
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:15.766771+00:00
-- url     : https://prove2.me/theorems/b6a756ed-0d05-472b-a791-56608c19cb9b
-- title:
--   Lemma B.1(e), Appendix p. 6 — Schur complements of inverse ZP-matrices are inverse ZP-matrices and nonnegative
-- statement:
--   Let $Y$ be a square matrix with block decomposition $Y=\begin{pmatrix}A&B\\C&D\end{pmatrix}$, where $A=Y_{S,S}$ and $D=Y_{\bar S,\bar S}$ are square, for an index set $S$ and its complement $\bar S$. If $A$ is nonsingular and $Y$ is the inverse of a ZP-matrix, then the Schur complement of $A$,
--   $$D-CA^{-1}B,$$
--   is itself the inverse of a ZP-matrix, and hence $D-CA^{-1}B\ge 0$ entrywise.
--
--   This is the closure of the class of inverse M-matrices under Schur complements.
--
--   **Formalization Note** The blocks are principal and off-diagonal submatrices of $Y$ on the subtypes $S$ and $\bar S$ of the index type, so no ordering of the indices is fixed. "$Y$ is the inverse of a ZP-matrix" is $YZ=I$ for some ZP-matrix $Z$.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), Online Appendix p. 6 (PDF 26), Lemma B.1(e)

import Mathlib
import Definitions.Def_PriceRobust_Stability_ZPMatrix

open Matrix

namespace PriceRobust.Stability

theorem lemma_B1_e {n : Type*} [Fintype n] [DecidableEq n]
    (Y : Matrix n n ℝ) (S : Finset n)
    (hA : IsUnit (Y.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∈ S} => x.1)).det)
    (hY : ∃ Z : Matrix n n ℝ, IsZPMatrix Z ∧ Y * Z = 1) :
    let A := Y.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∈ S} => x.1)
    let B := Y.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∉ S} => x.1)
    let C := Y.submatrix (fun x : {l // l ∉ S} => x.1) (fun x : {l // l ∈ S} => x.1)
    let D := Y.submatrix (fun x : {l // l ∉ S} => x.1) (fun x : {l // l ∉ S} => x.1)
    (∃ Z' : Matrix {l // l ∉ S} {l // l ∉ S} ℝ, IsZPMatrix Z' ∧ (D - C * A⁻¹ * B) * Z' = 1) ∧
      ∀ l m, 0 ≤ (D - C * A⁻¹ * B) l m := by sorry

end PriceRobust.Stability
