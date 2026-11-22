-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_5_3
-- name    : SKHessianAscent.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:13:39.161413+00:00
-- url     : https://prove2.me/theorems/14206aee-518b-4f75-9213-b96fc2d8098a
-- title:
--   Lemma 5.3 — mixed Lipschitzness of $\nabla_A\Phi_{a,W,T}$ in $(a,W,T)$ for chaining
-- statement:
--   There is a universal constant $C>0$ with the following property. Fix $\beta,\gamma_Y,C_{\mathrm{op}}>0$ and let $C_1=1+\beta C_{\mathrm{op}}$. Let $A$ be symmetric with $\|A\|_{\mathrm{op}}\le C_{\mathrm{op}}$, let $a,\widetilde a\in[0,1]$, $W,\widetilde W\in\mathcal D_n([0,1])$, and $T,\widetilde T\in\mathcal D_n(\mathbb R)$ with $\|T\|_{L^2},\|\widetilde T\|_{L^2}\le1$. Let $\nabla_A\Phi_{a,W,T}(A)$ be the gradient on $\mathrm{Sym}_n(\mathbb R)$ of the functional (5.2) with respect to $\langle H,K\rangle=\mathrm{tr}_n(HK)$. Then
--
--   $$
--   \big\|\nabla_A\Phi_{a,W,T}(A)-\nabla_A\Phi_{\widetilde a,\widetilde W,\widetilde T}(A)\big\|_{L^2}\le C\beta\Big[\gamma_Y^{-2}|a-\widetilde a|+\big(C_1\gamma_Y^{-2}+\gamma_Y^{-3/2}\big)\|W-\widetilde W\|_{\mathrm{op}}+\gamma_Y^{-3/2}\|T-\widetilde T\|_{L^2}\Big].
--   $$
--
--   Consequently, $\|\nabla_A\Phi_{a,W,T}(A)\|_{L^2}\le C\beta\gamma_Y^{-3/2}\|T\|_{L^2}$.
--
--   This is the increment estimate for the Gaussian process $(a,W,T)\mapsto\Phi_{a,W,T}(A)$ used in the chaining bound of Theorem 5.4.
--
--   **Formalization Note** The statement asserts that $A\mapsto\Phi_{a,W,T}(\mathrm{symPart}(A))$ is differentiable at $A$, and the bounds are for any symmetric $G$ representing the derivative, $d\Phi[H]=\mathrm{tr}_n(GH)$ for all symmetric $H$ (such $G$ is the gradient and is unique).
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 5.3, eqs. (5.16)–(5.17), p. 28

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Reciprocal

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
open scoped Matrix.Norms.L2Operator

namespace SKHessianAscent

theorem lemma_5_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (β γ Cop : ℝ), 0 < β → 0 < γ → 0 < Cop →
        ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → opNorm A ≤ Cop →
          ∀ (a a' : ℝ) (w w' τ τ' : Fin n → ℝ),
            0 ≤ a → a ≤ 1 → 0 ≤ a' → a' ≤ 1 →
            (∀ i, 0 ≤ w i ∧ w i ≤ 1) → (∀ i, 0 ≤ w' i ∧ w' i ≤ 1) →
            schatten2 (Matrix.diagonal τ) ≤ 1 → schatten2 (Matrix.diagonal τ') ≤ 1 →
              DifferentiableAt ℝ (fun X => PhiFun β γ a w τ (symPart X)) A ∧
              DifferentiableAt ℝ (fun X => PhiFun β γ a' w' τ' (symPart X)) A ∧
              ∀ G G' : Matrix (Fin n) (Fin n) ℝ, G.IsSymm → G'.IsSymm →
                (∀ H : Matrix (Fin n) (Fin n) ℝ, H.IsSymm →
                  fderiv ℝ (fun X => PhiFun β γ a w τ (symPart X)) A H = ntr (G * H)) →
                (∀ H : Matrix (Fin n) (Fin n) ℝ, H.IsSymm →
                  fderiv ℝ (fun X => PhiFun β γ a' w' τ' (symPart X)) A H = ntr (G' * H)) →
                  schatten2 (G - G') ≤
                    C * β * (γ ^ (-2 : ℤ) * |a - a'| +
                      ((1 + β * Cop) * γ ^ (-2 : ℤ) + γ ^ (-(3 : ℝ) / 2)) *
                        opNorm (Matrix.diagonal w - Matrix.diagonal w') +
                      γ ^ (-(3 : ℝ) / 2) * schatten2 (Matrix.diagonal τ - Matrix.diagonal τ')) ∧
                  schatten2 G ≤ C * β * γ ^ (-(3 : ℝ) / 2) * schatten2 (Matrix.diagonal τ) := by sorry

end SKHessianAscent
