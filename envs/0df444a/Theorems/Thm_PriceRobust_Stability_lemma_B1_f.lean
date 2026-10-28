-- Prove2me | Theorems.Thm_PriceRobust_Stability_lemma_B1_f
-- name    : PriceRobust.Stability.lemma_B1_f
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:07.52298+00:00
-- url     : https://prove2.me/theorems/6d3b3983-0349-4999-aa7a-f8170b4b2744
-- title:
--   Lemma B.1(f), Appendix p. 6 — X_{S̄,S} X_{S,S}⁻¹ X_{S,S̄} ≥ 0 for the inverse X of a symmetric ZP-matrix
-- statement:
--   Let $Y$ be a symmetric ZP-matrix, written in blocks as $Y=\begin{pmatrix}A&B\\B^\top&D\end{pmatrix}$ with $A$ the $|\bar S|\times|\bar S|$ block and $D$ the $|S|\times|S|$ block, and let $X=Y^{-1}$. Then
--   $$X_{\bar S,S}\,X_{S,S}^{-1}\,X_{S,\bar S}\ \ge\ 0$$
--   entrywise.
--
--   **Formalization Note** $S$ is any finite subset of the index type and $\bar S$ its complement; the submatrices are taken on these subtypes. $X$ is Mathlib's inverse of $Y$, which is invertible since $Y$ is a P-matrix.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), Online Appendix p. 6 (PDF 26), Lemma B.1(f)

import Mathlib
import Definitions.Def_PriceRobust_Stability_ZPMatrix

open Matrix

namespace PriceRobust.Stability

theorem lemma_B1_f {n : Type*} [Fintype n] [DecidableEq n]
    (Y X : Matrix n n ℝ) (S : Finset n)
    (hsymm : Y.IsSymm) (hY : IsZPMatrix Y) (hX : X = Y⁻¹) :
    ∀ l m, 0 ≤ (X.submatrix (fun x : {l // l ∉ S} => x.1) (fun x : {l // l ∈ S} => x.1) *
        (X.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∈ S} => x.1))⁻¹ *
        X.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∉ S} => x.1)) l m := by sorry

end PriceRobust.Stability
