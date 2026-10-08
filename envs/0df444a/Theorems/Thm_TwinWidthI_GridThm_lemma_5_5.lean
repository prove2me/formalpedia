-- Prove2me | Theorems.Thm_TwinWidthI_GridThm_lemma_5_5
-- name    : TwinWidthI.GridThm.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:51.874208+00:00
-- url     : https://prove2.me/theorems/385231f7-e5a2-48a7-a0f4-b96caef58ca0
-- title:
--   Lemma 5.5 — a matrix is mixed if and only if it contains a corner
-- statement:
--   Let $M=(m_{i,j})$ be an $n\times m$ matrix over a finite alphabet. Call $M$ *mixed* if it is neither vertical (all rows equal) nor horizontal (all columns equal), and call a *corner* any mixed $2\times 2$ submatrix $(m_{i,j},m_{i+1,j},m_{i,j+1},m_{i+1,j+1})$ on two consecutive rows and two consecutive columns. Then
--
--   $$M\ \text{is mixed}\iff M\ \text{contains a corner}.$$
--
--   Corners localize mixedness: they play for mixed minors the role that the entries $1$ play in the Marcus–Tardos theorem, and they drive Lemma 5.6 and Lemma 5.7.
--
--   **Formalization Note** The whole matrix is the zone `univ × univ`; `IsCorner M i j` asserts that rows `i, i+1` and columns `j, j+1` exist and that the $2\times2$ zone they span is mixed. For $n\le 1$ or $m\le1$ both sides are false.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:20, Lemma 5.5

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.GridThm

/-- Lemma 5.5, p. 3:20: a matrix is mixed if and only if it contains a corner. -/
theorem lemma_5_5 {A : Type*} [Fintype A] {n m : ℕ} (M : Matrix (Fin n) (Fin m) A) :
    IsMixed M Finset.univ Finset.univ ↔ ∃ i j, IsCorner M i j := by sorry

end TwinWidthI.GridThm
