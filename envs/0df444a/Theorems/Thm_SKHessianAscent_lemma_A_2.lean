-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_A_2
-- name    : SKHessianAscent.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:22:32.161262+00:00
-- url     : https://prove2.me/theorems/407cc16d-252c-4b14-ad5c-5db7910484d8
-- title:
--   Lemma A.2 — the TAP free limit for $\beta<1$: spectral gap and $\mathbf E_{M_n}[D(aI_n-\beta S+D)^{-2}D]=I_n/(1-\beta^2\mathrm{tr}_n(D^{-2}))$
-- statement:
--   Let $S$ be a semicircular element free from $(M_n(\mathbb C),\mathrm{tr}_n)$ in $(\mathcal M_n,\tau_n)$ and $\mathbf E_{M_n}$ the trace-preserving conditional expectation onto $M_n(\mathbb C)$. Let $0<\beta<1$, let $D\succeq I_n$ be a real diagonal matrix, and $a=\beta^2\mathrm{tr}_n(D^{-1})$. Then
--   $$aI_n-\beta S+D\succeq(1-\beta)^2I_n.\tag{A.1}$$
--   For all
--   $$0<\gamma_Y\le\frac{(1-\beta)^4}{4(1+2\beta^2)^2},\tag{A.2}$$
--   it is true uniformly in $D\succeq I_n$ that
--   $$(I_n+D^{-1}(aI_n-\beta S))(I_n+(aI_n-\beta S)D^{-1})\succeq4\gamma_YI_n.$$
--   For every such $D$ and $a$,
--   $$\mathbf E_{M_n}\big[D(aI_n-\beta S+D)^{-2}D\big]=\frac{I_n}{1-\beta^2\mathrm{tr}_n(D^{-2})}.$$
--
--   **Formalization Note** Operator inequalities $X\succeq c$ in $\mathcal M_n$ are: $X$ is self-adjoint and its spectrum lies in $[c,\infty)$. The statement holds for every standard free semicircular family realizing $S$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Appendix A.2, Lemma A.2, (A.1)–(A.2), p. 46

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Reciprocal
import Definitions.Def_SKHessianAscent_FreeModel

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace SKHessianAscent

theorem lemma_A_2 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) (d : Fin n → ℝ) (hd : ∀ i, 1 ≤ d i)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : GueIdx n → H →L[ℂ] H) (ω : H) (hs : FreeWeaver.Walk.IsStdFreeSemicircular s ω) :
    let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (d i : ℂ)
    let Di : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => ((d i : ℂ))⁻¹
    let a : ℝ := β ^ 2 * ((∑ i, (d i)⁻¹) / n)
    let X := gueOp ((a : ℂ) • 1 + D) (-(β : ℂ) • 1) 1 s
    SpecGe X ((1 - β) ^ 2) ∧
    (∀ γ : ℝ, 0 < γ → γ ≤ (1 - β) ^ 4 / (4 * (1 + 2 * β ^ 2) ^ 2) →
      SpecGe (gueOp (1 + (a : ℂ) • Di) (-(β : ℂ) • Di) 1 s *
        gueOp (1 + (a : ℂ) • Di) (-(β : ℂ) • 1) Di s) (4 * γ)) ∧
    FreeWeaver.Walk.slice ω (gueOp D 0 1 s * Ring.inverse X ^ 2 * gueOp D 0 1 s) =
      (((1 - β ^ 2 * ((∑ i, ((d i)⁻¹) ^ 2) / n))⁻¹ : ℝ) : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ) := by sorry

end SKHessianAscent
