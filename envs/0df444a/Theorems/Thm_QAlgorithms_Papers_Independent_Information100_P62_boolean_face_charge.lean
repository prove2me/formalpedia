-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_boolean_face_charge
-- name    : QAlgorithms.Papers.Independent.Information100.P62.boolean_face_charge
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:59:21.955183+00:00
-- url     : https://prove2.me/theorems/5a7a6b51-e86d-43ff-ad3e-e28bda9e275a
-- title:
--   Lemma 5.6: Boolean cube face incidence charge
-- statement:
--   Let $\varnothing\ne Y\subseteq\{0,1\}^n$ and $q\ge1$. Suppose each $y\in Y$ belongs to at least $q$ distinct cube faces contained in $Y$. Then $q\le|Y|\le2^n$. For any choice of exactly $q$ such distinct faces $\mathcal F_y$ at each $y$,
--   $$\sum_{y\in Y}\sum_{F\in\mathcal F_y}\frac1{|F|}\ge s_n(q).$$
--   Faces are products of singleton or two-element coordinate sets. This is the combinatorial charge bound used for code converses.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 50, Lemma 5.6: Boolean cube face incidence charge

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.50, 58, 59, 60, Lemma 5.6: Boolean cube face incidence charge. -/
theorem boolean_face_charge (n q : ℕ) (hq : 0 < q) (Y : Finset (Qubits n)) (hY : Y.Nonempty)
    (hfaces : ∀ y ∈ Y, q ≤ (univ.filter (fun F : Fin n → Fin 3 => y ∈ faceVertices F ∧ faceVertices F ⊆ Y)).card) :
    q ≤ Y.card ∧ Y.card ≤ 2 ^ n ∧
    ∀ F : Qubits n → Finset (Fin n → Fin 3),
      (∀ y ∈ Y, (F y).card = q ∧ ∀ f ∈ F y, y ∈ faceVertices f ∧ faceVertices f ⊆ Y) →
      (charge n q : ℝ) ≤ ∑ y ∈ Y, ∑ f ∈ F y, ((faceVertices f).card : ℝ)⁻¹ := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
