-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_5_7
-- name    : SKHessianAscent.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:15:55.95281+00:00
-- url     : https://prove2.me/theorems/c58fd15b-64a8-42d9-b771-00b0e07c2555
-- title:
--   Lemma 5.7 — smooth test transfer: $\mathbf E f$ of the GOE block matrix versus its free limit, for $f\in W^{6,1}(\mathbb R)$
-- statement:
--   Let $S$ be a semicircular element free from $(M_n(\mathbb C),\mathrm{tr}_n)$ in $(\mathcal M_n,\tau_n)$ and $\mathbf E_{M_n}$ the trace-preserving conditional expectation onto $M_n(\mathbb C)$. There is a universal constant $C>0$ such that the following holds. Fix $a\in[0,1]$, $\beta>0$, $\gamma_Y>0$ and a diagonal $W=D^{-1}$ with entries in $[0,1]$, and write $B(X)=\begin{pmatrix}0&I_n+D^{-1}(aI_n-\beta X)\\I_n+(aI_n-\beta X)D^{-1}&0\end{pmatrix}$. Then every real $f\in L^1(\mathbb R)$ that is six times weakly differentiable, with all derivatives $f^{(j)}\in L^1(\mathbb R)$, satisfies, for $A\sim\mathrm{GOE}(n)$,
--   $$\Big\|\mathbf E_A\,f\big(\gamma_Y^{-1/2}B(A)\big)-(\mathrm{id}_2\otimes\mathbf E_{M_n})\big[f\big(\gamma_Y^{-1/2}B(S)\big)\big]\Big\|_{\mathrm{op}}\le\frac Cn\Big[\beta^2\gamma_Y^{-1}\sum_{j=0}^4\|f^{(j)}\|_{L^1(\mathbb R)}+\beta^4\gamma_Y^{-2}\sum_{j=0}^6\|f^{(j)}\|_{L^1(\mathbb R)}\Big].\tag{5.31}$$
--
--   **Formalization Note** "Six times weakly differentiable with derivatives in $L^1$" is given by functions $g_0=f,g_1,\dots,g_6\in L^1(\mathbb R)$ with $g_j(x)=g_j(0)+\int_0^xg_{j+1}$ for $j<6$; this fixes the continuous representative of $f$. $f(B(S))$ is the continuous functional calculus of the self-adjoint element $B(S)$ of $M_{2n}(\mathcal A)$, written with the complex functional calculus applied to $x\mapsto f(\mathrm{Re}\,x)$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §5.3, Lemma 5.7, (5.31), pp. 33–34

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Reciprocal
import Definitions.Def_SKHessianAscent_FreeModel

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace SKHessianAscent

theorem lemma_5_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (β a γ : ℝ) (w : Fin n → ℝ), 0 < β → 0 ≤ a → a ≤ 1 → 0 < γ →
        (∀ i, 0 ≤ w i ∧ w i ≤ 1) →
        ∀ g : Fin 7 → ℝ → ℝ, (∀ j, Integrable (g j)) →
          (∀ (j : Fin 6) (x : ℝ), g j.castSucc x = g j.castSucc 0 + ∫ t in (0 : ℝ)..x, g j.succ t) →
          ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
            (s : GueIdx n → H →L[ℂ] H) (ω : H), FreeWeaver.Walk.IsStdFreeSemicircular s ω →
            let EA : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fun k l =>
              ((∫ A, matFun (g 0) ((Real.sqrt γ)⁻¹ • blockArg β a w (Matrix.of A)) k l
                ∂(RandMatDisc.goe n) : ℝ) : ℂ)
            let F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
              FreeWeaver.Walk.slice ω
                (cfc (fun x : ℂ => ((g 0 x.re : ℝ) : ℂ))
                  ((((Real.sqrt γ)⁻¹ : ℝ) : ℂ) • (blockPencil β a w).op s))
            FreeWeaver.Walk.opNorm (EA - F) ≤
              C / n * (β ^ 2 * γ⁻¹ *
                  (∑ j ∈ Finset.univ.filter (fun j : Fin 7 => (j : ℕ) ≤ 4), ∫ x, |g j x|) +
                β ^ 4 * γ ^ (-2 : ℤ) * ∑ j : Fin 7, ∫ x, |g j x|) := by sorry

end SKHessianAscent
