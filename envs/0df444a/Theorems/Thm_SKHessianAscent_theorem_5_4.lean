-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_5_4
-- name    : SKHessianAscent.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:14:11.429828+00:00
-- url     : https://prove2.me/theorems/f259329f-b45c-4399-9d20-ec84f515fbab
-- title:
--   Theorem 5.4 — chaining bound for the fluctuations of the reciprocal extension $\Phi_{a,W,T}$, uniformly over $(a,W,T)$
-- statement:
--   There are universal constants $C_{\mathrm{ch}},C_{\mathrm{tail}}>0$ with the following property. Fix $\beta,\gamma_Y,C_{\mathrm{op}}>0$, let $C_1=1+\beta C_{\mathrm{op}}$ and $A\sim\mathrm{GOE}(n)$. Let $\Pi_{C_{\mathrm{op}}}$ be the metric projection, with respect to $\|\cdot\|_{L^2}$, onto $\{M\in\mathrm{Sym}_n(\mathbb R):\|M\|_{\mathrm{op}}\le C_{\mathrm{op}}\}$, and $\overline A=\Pi_{C_{\mathrm{op}}}(A)$. With $\Phi_{a,W,T}$ the functional (5.2), define
--
--   $$
--   \mathcal J=[0,1]\times\mathcal D_n([0,1])\times\{T\in\mathcal D_n(\mathbb R):\|T\|_{L^2}=1\},\qquad Z_{a,W,T}=\Phi_{a,W,T}(\overline A)-\mathbf E_A\big[\Phi_{a,W,T}(\overline A)\big].
--   $$
--
--   Then
--
--   $$
--   \mathbf E_A\Big[\sup_{(a,W,T)\in\mathcal J}|Z_{a,W,T}|\Big]\le\frac{C_{\mathrm{ch}}\beta}{\sqrt n}\Big((1+C_1)\gamma_Y^{-2}+\gamma_Y^{-3/2}\Big),
--   $$
--
--   and for every $p\in(0,1)$,
--
--   $$
--   \Pr_A\Big\{\sup_{(a,W,T)\in\mathcal J}|Z_{a,W,T}|\le\frac{C_{\mathrm{ch}}\beta}{\sqrt n}\Big((1+C_1)\gamma_Y^{-2}+\gamma_Y^{-3/2}\Big)+\frac{C_{\mathrm{tail}}\beta\gamma_Y^{-3/2}}{n}\sqrt{\log\frac2p}\Big\}\ge1-p.
--   $$
--
--   The theorem gives uniform concentration of the regularized resolvent diagonal over all parameters at once; it is the first of the two inputs to Corollary 5.9.
--
--   **Formalization Note** The universal constants are quantified before $n$. The supremum is the real supremum over the parameter set (bounded by Proposition 5.2(a)); the probability bound is on the outer measure of the complementary event; expectations are Bochner integrals over the published `RandMatDisc.goe n`.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Theorem 5.4, eqs. (5.20)–(5.23), p. 30

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Reciprocal

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
open scoped Matrix.Norms.L2Operator

namespace SKHessianAscent

theorem theorem_5_4 :
    ∃ Cch Ctail : ℝ, 0 < Cch ∧ 0 < Ctail ∧
      ∀ (n : ℕ) (β γ Cop : ℝ), 0 < β → 0 < γ → 0 < Cop →
        let Z : (ℝ × (Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → Fin n → ℝ) → ℝ := fun θ A =>
          PhiFun β γ θ.1 θ.2.1 θ.2.2 (opBallProj Cop (Matrix.of A)) -
            ∫ A', PhiFun β γ θ.1 θ.2.1 θ.2.2 (opBallProj Cop (Matrix.of A')) ∂(RandMatDisc.goe n)
        let S : (Fin n → Fin n → ℝ) → ℝ := fun A => ⨆ θ : paramSet n, |Z θ.1 A|
        let b : ℝ := Cch * β / Real.sqrt n *
          ((1 + (1 + β * Cop)) * γ ^ (-2 : ℤ) + γ ^ (-(3 : ℝ) / 2))
        ∫ A, S A ∂(RandMatDisc.goe n) ≤ b ∧
          ∀ p : ℝ, 0 < p → p < 1 →
            RandMatDisc.goe n {A |
                b + Ctail * β * γ ^ (-(3 : ℝ) / 2) / n * Real.sqrt (Real.log (2 / p)) < S A} ≤
              ENNReal.ofReal p := by sorry

end SKHessianAscent
