-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_dfp_product_form
-- name    : VarStorageQN.LeastChange.dfp_product_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:28.580989+00:00
-- url     : https://prove2.me/theorems/2a97c886-4d66-41c4-afa8-021cb58dcec5
-- title:
--   (A.9) — product form of the dfp update and its positivity
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $B=B^*$ a self-adjoint bounded operator, $y,s\in\mathcal H$, and $a=\langle y,s\rangle$. Let
--
--   $$B_{\mathrm{dfp}}=B+\frac{[y-Bs,y]+[y,y-Bs]}{a}-\frac{\langle y-Bs,s\rangle}{a^2}[y,y]\tag{A.8}$$
--
--   be the dfp update. Then:
--
--   1. if $a\ne0$, it has the product form
--   $$B_{\mathrm{dfp}}=\Big[I-\frac{[y,s]}{a}\Big]\,B\,\Big[I-\frac{[s,y]}{a}\Big]+\frac{[y,y]}{a};\tag{A.9}$$
--   2. if $B$ is positive ($\langle Bu,u\rangle>0$ for $u\ne0$) and $a>0$, then $B_{\mathrm{dfp}}$ is self-adjoint and positive.
--
--   The second statement is the hereditary positivity of the dfp update, which the paper derives from the form (A.9).
--
--   **Formalization Note** The paper states the positivity claim and gives (A.9) as "the following form of formula (A.8)"; the identity is stated under the paper's standing assumption that $B$ is self-adjoint (without it the two sides differ) and under $a\ne0$, which the paper's divisions require. Positivity is the strict predicate `IsPositiveStrict`. Division by $a$ is multiplication by $a^{-1}$.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 30, Annex, (A.8) and (A.9)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_Bracket

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- (A.9), p. 30: for self-adjoint `B` and `⟨y,s⟩ ≠ 0` the dfp operator (A.8) has the product
form (A.9); if moreover `B` is positive and `⟨y,s⟩ > 0`, `B_dfp` is self-adjoint and positive. -/
theorem dfp_product_form (B : H →L[ℝ] H) (hB : IsSelfAdjoint B) (y s : H) :
    let a := ⟪y, s⟫_ℝ
    let r := y - B s
    let Bdfp : H →L[ℝ] H :=
      B + a⁻¹ • (bracket r y + bracket y r) - (⟪r, s⟫_ℝ / a ^ 2) • bracket y y
    (a ≠ 0 →
      Bdfp = (1 - a⁻¹ • bracket y s) ∘L B ∘L (1 - a⁻¹ • bracket s y) + a⁻¹ • bracket y y) ∧
    (IsPositiveStrict B → 0 < a → IsSelfAdjoint Bdfp ∧ IsPositiveStrict Bdfp) := by sorry

end VarStorageQN.LeastChange
