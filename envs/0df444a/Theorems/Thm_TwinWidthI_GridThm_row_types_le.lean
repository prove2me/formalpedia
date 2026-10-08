-- Prove2me | Theorems.Thm_TwinWidthI_GridThm_row_types_le
-- name    : TwinWidthI.GridThm.row_types_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:04.457288+00:00
-- url     : https://prove2.me/theorems/bd4cff0d-ba7f-44c5-80a1-5a95bbcb2850
-- title:
--   Proof of Theorem 5.4, p. 3:22 — at most α^{t′+1} row types of R_i outside its mixed zones
-- statement:
--   Let $M$ be an $n\times m$ matrix over an alphabet $A$ of size $\alpha$, with $m\ge1$. Let $(\mathcal R,\mathcal C)$ be a division of $M$ with mixed value at most $t'$, and let $R_i\in\mathcal R$. Restrict every row of $R_i$ to the columns that lie in column parts $C_j$ for which the zone $R_i\cap C_j$ is not mixed. Then the number of distinct restricted rows is at most $\alpha^{t'+1}$:
--
--   $$\#\bigl\{\,(m_{a,j})_{j\in J}\ :\ a\in R_i\,\bigr\}\ \le\ \alpha^{t'+1},\qquad J=\bigcup\{C_j\in\mathcal C:\ R_i\cap C_j\text{ not mixed}\}.$$
--
--   This count is the step of the proof of Theorem 5.4 that makes the refined partition $(\mathcal R'^s,\mathcal C'^s)$ an $\alpha^{t'+1}$-refinement of $(\mathcal R^s,\mathcal C^s)$.
--
--   **Formalization Note** A restricted row is a function from the subtype of columns $j$ whose part $C.\mathrm{part}(j)$ forms a non-mixed zone with $R_i$ to $A$; the statement counts the image of $R_i$ under restriction. Added hypothesis $m\ge1$: with $m=0$ and an empty alphabet the bound $\alpha^{t'+1}=0$ would fail for a non-empty $R_i$ (the paper's matrices are non-empty).
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:22, proof of Theorem 5.4 ("there are at most α^r ⩽ α^{t′+1} different rows in R_i")

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.GridThm

open Classical in
/-- Proof of Theorem 5.4, p. 3:22: if a division `(R, C)` has mixed value at most `t'`, then the
rows of a row part `X ∈ R`, restricted to the columns lying in column parts `Y` for which the zone
`X ∩ Y` is not mixed, take at most `α ^ (t' + 1)` distinct values, where `α` is the alphabet
size. Counting uses classical decidability. -/
theorem row_types_le {A : Type*} [Fintype A] {n m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin m) A)
    (R : Finpartition (Finset.univ : Finset (Fin n)))
    (C : Finpartition (Finset.univ : Finset (Fin m)))
    (hR : IsDivision R) (hC : IsDivision C) (t' : ℕ) (hmv : MixedValueLE M R C t')
    (X : Finset (Fin n)) (hX : X ∈ R.parts) :
    (X.image (fun i => fun j : {j : Fin m // ¬ IsMixed M X (C.part j)} => M i j)).card ≤
      Fintype.card A ^ (t' + 1) := by sorry

end TwinWidthI.GridThm
