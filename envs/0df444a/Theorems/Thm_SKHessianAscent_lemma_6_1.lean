-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_6_1
-- name    : SKHessianAscent.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:17:22.830644+00:00
-- url     : https://prove2.me/theorems/b2b9bf60-8755-4cff-869d-747bef60d100
-- title:
--   Lemma 6.1 — basic resolvent bounds on the good set: $\|Q\|,\|\widehat Q\|\le c^{-1}$, $\|DQ\|,\|D\widehat Q\|\le1+(3\beta+3\beta^2)/c$
-- statement:
--   Fix $0<\beta<1$ and $c>0$, and let $A$ be a symmetric real $n\times n$ matrix with $\|A\|_{\mathrm{op}}\le3$. Write $D=D(m)=\mathrm{diag}(1/(1-m_i^2))$, $a(m)=\beta^2\mathrm{tr}_n(D(m)^{-1})$, $Q(m)=(a(m)I_n-\beta A+D(m))^{-1}$ and $\widehat Q(m)=(a(m)I_n-\beta A+D(m)-\tfrac{2\beta^2}{n}mm^{\mathsf T})^{-1}$, and let $\mathcal S_{\beta,A}(c)$ be the safe set. Put $\kappa=1+\frac{3\beta+3\beta^2}{c}$. Then for every $m\in\mathcal S_{\beta,A}(c)$, both $Q(m)$ and $\widehat Q(m)$ are positive definite and
--
--   1. $\|Q(m)\|_{\mathrm{op}},\ \|\widehat Q(m)\|_{\mathrm{op}}\le c^{-1}$;
--   2. $\|D(m)Q(m)\|_{\mathrm{op}},\ \|D(m)\widehat Q(m)\|_{\mathrm{op}}\le\kappa$;
--   3. $\|D(m)Q(m)^2\|_{\mathrm{op}},\ \|D(m)\widehat Q(m)^2\|_{\mathrm{op}}\le c^{-1}\kappa$;
--   4. $\|D(m)Q(m)^2D(m)\|_{\mathrm{op}},\ \|D(m)\widehat Q(m)^2D(m)\|_{\mathrm{op}}\le\kappa^2$.
--
--   These bounds are the starting point of every estimate of Section 6.
--
--   **Formalization Note** All constants are the explicit ones of the paper. The statement is for one matrix and one point; $n$ is arbitrary.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 6.1, eq. (6.6), p. 37

import Mathlib
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Resolvent

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_6_1 (β c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hA3 : opNorm A ≤ 3)
    (m : Fin n → ℝ) (hm : m ∈ safeSet β A c) :
    let κ : ℝ := 1 + (3 * β + 3 * β ^ 2) / c
    (Qres β A m).PosDef ∧ (Qhat β A m).PosDef ∧
      opNorm (Qres β A m) ≤ c⁻¹ ∧ opNorm (Qhat β A m) ≤ c⁻¹ ∧
      opNorm (Dmat m * Qres β A m) ≤ κ ∧ opNorm (Dmat m * Qhat β A m) ≤ κ ∧
      opNorm (Dmat m * Qres β A m ^ 2) ≤ c⁻¹ * κ ∧ opNorm (Dmat m * Qhat β A m ^ 2) ≤ c⁻¹ * κ ∧
      opNorm (Dmat m * Qres β A m ^ 2 * Dmat m) ≤ κ ^ 2 ∧
      opNorm (Dmat m * Qhat β A m ^ 2 * Dmat m) ≤ κ ^ 2 := by sorry

end SKHessianAscent
