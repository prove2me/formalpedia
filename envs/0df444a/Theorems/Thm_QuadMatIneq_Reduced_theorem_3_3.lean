-- Prove2me | Theorems.Thm_QuadMatIneq_Reduced_theorem_3_3
-- name    : QuadMatIneq.Reduced.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:50.08198+00:00
-- url     : https://prove2.me/theorems/1030fcf2-c2a6-4e4a-998b-d146ee60d55b
-- title:
--   Theorem 3.3, p. 8 — parameterization of 𝒵_r(Π) and 𝒵_r^+(Π) for Π ∈ 𝚷_{q,r} via contractions S and free T, formula (3.7)
-- statement:
--   Let $\Pi\in\boldsymbol\Pi_{q,r}$.
--
--   1. $Z\in\mathcal Z_r(\Pi)$ if and only if there exist $S, T\in\mathbb R^{r\times q}$ with $S^\top S\le I$ such that
--   $$Z = -\Pi_{22}^\dagger\Pi_{21} + \big((-\Pi_{22})^\dagger\big)^{1/2} S\,(\Pi\,|\,\Pi_{22})^{1/2} + (I - \Pi_{22}^\dagger\Pi_{22})T. \tag{3.7}$$
--   2. Assume that $\mathcal Z_r^+(\Pi)$ is nonempty. Then $Z\in\mathcal Z_r^+(\Pi)$ if and only if $Z$ is of the form (3.7) for some $S, T\in\mathbb R^{r\times q}$ with $S^\top S < I$.
--
--   Here $M^{1/2}$ denotes the positive semidefinite square root of a positive semidefinite matrix $M$. The theorem gives an explicit description of all solutions of a QMI, including the unbounded case $\Pi_{22}$ singular, and is the basis of the image results of Section 3.3.
--
--   **Formalization Note** The square roots are Mathlib's continuous-functional-calculus square root `CFC.sqrt` for the Loewner order on matrices; both arguments are positive semidefinite for $\Pi\in\boldsymbol\Pi_{q,r}$. Part (b) takes the printed hypothesis "$\mathcal Z_r^+(\Pi)$ is nonempty"; its equivalence with $\Pi\,|\,\Pi_{22}>0$ is Theorem 3.2(d) and is not part of this statement.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 3.3, p. 8, (3.7)

import Mathlib
import Definitions.Def_QuadMatIneq_Reduced_QMI
open Matrix
open scoped MatrixOrder

namespace QuadMatIneq.Reduced

theorem theorem_3_3 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (∀ Z : Matrix κ ι ℝ, Z ∈ ZSet P ↔
      ∃ S T : Matrix κ ι ℝ, (1 - Sᵀ * S).PosSemidef ∧
        Z = -(pinv P.toBlocks₂₂ * P.toBlocks₂₁)
          + CFC.sqrt (pinv (-P.toBlocks₂₂)) * S * CFC.sqrt (schur P)
          + (1 - pinv P.toBlocks₂₂ * P.toBlocks₂₂) * T) ∧
    ((ZPlus P).Nonempty →
      ∀ Z : Matrix κ ι ℝ, Z ∈ ZPlus P ↔
        ∃ S T : Matrix κ ι ℝ, (1 - Sᵀ * S).PosDef ∧
          Z = -(pinv P.toBlocks₂₂ * P.toBlocks₂₁)
            + CFC.sqrt (pinv (-P.toBlocks₂₂)) * S * CFC.sqrt (schur P)
            + (1 - pinv P.toBlocks₂₂ * P.toBlocks₂₂) * T) := by sorry

end QuadMatIneq.Reduced
