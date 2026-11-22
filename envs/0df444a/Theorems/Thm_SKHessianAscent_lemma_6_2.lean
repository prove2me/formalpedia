-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_6_2
-- name    : SKHessianAscent.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:17:57.710383+00:00
-- url     : https://prove2.me/theorems/79a4cb10-88e9-4542-abbe-0536bf802a89
-- title:
--   Lemma 6.2 — resolvent Lipschitz bounds on the good set: $\widehat Q$, $Q$, $\widehat Q^2$, $D\widehat Q$, $D\widehat Q^2D$ are $C_{\beta,c}/\sqrt n$-Lipschitz in $\|\cdot\|_{L^2}$
-- statement:
--   Fix $0<\beta<1$ and $c>0$, and let $A$ be a symmetric real $n\times n$ matrix with $\|A\|_{\mathrm{op}}\le3$. Write $D=D(m)=\mathrm{diag}(1/(1-m_i^2))$, $a(m)=\beta^2\mathrm{tr}_n(D(m)^{-1})$, $Q(m)=(a(m)I_n-\beta A+D(m))^{-1}$ and $\widehat Q(m)=(a(m)I_n-\beta A+D(m)-\tfrac{2\beta^2}{n}mm^{\mathsf T})^{-1}$, and let $\mathcal S_{\beta,A}(c)$ be the safe set. There is a constant $C_{\beta,c}$, independent of $n$ and $A$, such that for all $m,w\in\mathcal S_{\beta,A}(c)$ each of the maps
--
--   $$
--   G\in\big\{\ \widehat Q,\quad Q,\quad \widehat Q^2,\quad D\widehat Q,\quad D\widehat Q^2D\ \big\}
--   $$
--
--   satisfies
--
--   $$
--   \|G(m)-G(w)\|_{L^2}\le\frac{C_{\beta,c}}{\sqrt n}\,\|m-w\|_2 ,
--   $$
--
--   with the Euclidean distance on the input and the normalized Schatten 2-norm $\|X\|_{L^2}=\|X\|_F/\sqrt n$ on the output.
--
--   Because the safe set is not convex, these bounds are proved from the resolvent identity at the two endpoints rather than by integrating a derivative.
--
--   **Formalization Note** The Lipschitz norm on the (non-convex) set $\mathcal S_{\beta,A}(c)$ is written out as the two-point inequality. One constant serves the five maps.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 6.2, eq. (6.7), pp. 37–38

import Mathlib
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Resolvent

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_6_2 (β c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    ∃ K : ℝ,
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → opNorm A ≤ 3 →
        ∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
          schatten2 (Qhat β A m - Qhat β A w) ≤ K / Real.sqrt n * l2 (m - w) ∧
          schatten2 (Qres β A m - Qres β A w) ≤ K / Real.sqrt n * l2 (m - w) ∧
          schatten2 (Qhat β A m ^ 2 - Qhat β A w ^ 2) ≤ K / Real.sqrt n * l2 (m - w) ∧
          schatten2 (Dmat m * Qhat β A m - Dmat w * Qhat β A w) ≤ K / Real.sqrt n * l2 (m - w) ∧
          schatten2 (Dmat m * Qhat β A m ^ 2 * Dmat m - Dmat w * Qhat β A w ^ 2 * Dmat w) ≤
            K / Real.sqrt n * l2 (m - w) := by sorry

end SKHessianAscent
