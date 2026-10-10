-- Prove2me | Theorems.Thm_QuadMatIneq_Reduced_lemma_A_2
-- name    : QuadMatIneq.Reduced.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:08.536976+00:00
-- url     : https://prove2.me/theorems/538e95eb-6d71-43cf-a9d5-feaf4247c98a
-- title:
--   Lemma A.2, p. 27 — AM = B iff im B ⊆ im A and M = A†B + (I − A†A)T for some T
-- statement:
--   Let $A\in\mathbb R^{p\times q}$, $B\in\mathbb R^{p\times r}$ and $M\in\mathbb R^{q\times r}$. Then
--   $$AM = B \iff \operatorname{im} B\subseteq \operatorname{im} A \ \text{ and }\ M = A^\dagger B + (I_q - A^\dagger A)T \ \text{ for some } T\in\mathbb R^{q\times r}.$$
--
--   This is the classical description of all solutions of a linear matrix equation through the Moore–Penrose pseudo-inverse; it converts the factorization of Lemma A.1 into an explicit formula for the solution matrix.
--
--   **Formalization Note** The printed dimensions ($A\in\mathbb R^{q\times p}$, $B\in\mathbb R^{r\times p}$, $T\in\mathbb R^{r\times q}$) are inconsistent with the term $(I_q - A^\dagger A)T$. The statement here uses the dimensions forced by the formula and by its use in the proof of Theorem 3.3: $A$ has $q$ columns, $B$ has as many rows as $A$, and $M, T\in\mathbb R^{q\times r}$. The image inclusion is stated for the linear maps $v\mapsto Bv$ and $u\mapsto Au$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Lemma A.2, p. 27 (dimensions corrected, see Formalization Note)

import Mathlib
import Definitions.Def_QuadMatIneq_Reduced_QMI
open Matrix
open scoped MatrixOrder

namespace QuadMatIneq.Reduced

theorem lemma_A_2 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (A : Matrix α β ℝ) (B : Matrix α γ ℝ) (M : Matrix β γ ℝ) :
    A * M = B ↔
      LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin ∧
        ∃ T : Matrix β γ ℝ, M = pinv A * B + (1 - pinv A * A) * T := by sorry

end QuadMatIneq.Reduced
