-- Prove2me | Theorems.Thm_RFRidge_Basic_proposition_8
-- name    : RFRidge.Basic.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:21.327993+00:00
-- url     : https://prove2.me/theorems/77d25521-681a-4f00-9379-6d65aab9da2d
-- title:
--   Proposition 8, p. 40 — ‖(A+λI)^{-1/2}B^{1/2}‖ ≤ ‖(A+λI)^{-1/2}(B+λI)^{1/2}‖ ≤ (1−β)^{-1/2}, β < 1
-- statement:
--   Let $A,B$ be bounded self-adjoint positive operators on a Hilbert space and $\lambda>0$. Put
--   $$\beta=\lambda_{\max}\big[(B+\lambda I)^{-1/2}(B-A)(B+\lambda I)^{-1/2}\big].$$
--   Then $\beta<1$ and
--   $$\|(A+\lambda I)^{-1/2}B^{1/2}\|\le\|(A+\lambda I)^{-1/2}(B+\lambda I)^{1/2}\|\le(1-\beta)^{-1/2}.$$
--
--   The proposition turns a relative perturbation bound $\beta$ into a multiplicative bound between regularized operators; it is used in the analytic decomposition (Theorem 4).
--
--   **Formalization Note** $\lambda_{\max}$ is the supremum of $\langle f,Qf\rangle$ over $\|f\|\le1$ (App. A.1). The operators $(A+\lambda I)^{-1/2}$, $(B+\lambda I)^{\pm1/2}$ and $B^{1/2}$ are the continuous functional calculus of the real functions $t\mapsto(t+\lambda)^{-1/2}$, $t\mapsto\sqrt{t+\lambda}$ and $\sqrt t$, on a complex Hilbert space (see Proposition 4); separability is dropped. The page's "Note that $\beta<1$" is stated as a third conclusion; it also guarantees $(1-\beta)^{-1/2}$ is the power of a positive number.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Proposition 8, p. 40 (proof p. 41); λ_max, App. A.1 p. 17

import Mathlib
import Definitions.Def_RFRidge_Basic_LambdaMax

namespace RFRidge.Basic

/-- Proposition 8, p. 40: for positive bounded operators `A, B` on a Hilbert space and `λ > 0`,
`‖(A + λI)^{-1/2} B^{1/2}‖ ≤ ‖(A + λI)^{-1/2} (B + λI)^{1/2}‖ ≤ (1 − β)^{-1/2}` with
`β = λ_max[(B + λI)^{-1/2} (B − A) (B + λI)^{-1/2}]`, and `β < 1`. Every function of an operator is a
continuous functional calculus `cfc` of an explicit real function on a complex Hilbert space. -/
theorem proposition_8 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] E) (hA : 0 ≤ A) (hB : 0 ≤ B) (lam : ℝ) (hlam : 0 < lam) :
    let Alm : E →L[ℂ] E := cfc (fun t : ℝ => (t + lam) ^ (-(1 / 2 : ℝ))) A
    let Blm : E →L[ℂ] E := cfc (fun t : ℝ => (t + lam) ^ (-(1 / 2 : ℝ))) B
    let Blp : E →L[ℂ] E := cfc (fun t : ℝ => Real.sqrt (t + lam)) B
    let β : ℝ := lambdaMax (Blm * (B - A) * Blm)
    ‖Alm * CFC.sqrt B‖ ≤ ‖Alm * Blp‖ ∧ ‖Alm * Blp‖ ≤ (1 - β) ^ (-(1 / 2 : ℝ)) ∧ β < 1 := by sorry

end RFRidge.Basic
