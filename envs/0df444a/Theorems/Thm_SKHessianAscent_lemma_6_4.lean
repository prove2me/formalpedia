-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_6_4
-- name    : SKHessianAscent.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:18:30.27392+00:00
-- url     : https://prove2.me/theorems/9eb437b7-d789-4484-86cc-f066e1d7662d
-- title:
--   Lemma 6.4 — small diagonal error from the rank-one term: $\|\mathbf E_{\mathcal D_n}[D(\widehat Q^2-Q^2)D]\|_{L^2}\le C_{\beta,c}/\sqrt n$
-- statement:
--   Fix $0<\beta<1$ and $c>0$, and let $A$ be a symmetric real $n\times n$ matrix with $\|A\|_{\mathrm{op}}\le3$. Write $D=D(m)=\mathrm{diag}(1/(1-m_i^2))$, $a(m)=\beta^2\mathrm{tr}_n(D(m)^{-1})$, $Q(m)=(a(m)I_n-\beta A+D(m))^{-1}$ and $\widehat Q(m)=(a(m)I_n-\beta A+D(m)-\tfrac{2\beta^2}{n}mm^{\mathsf T})^{-1}$, and let $\mathcal S_{\beta,A}(c)$ be the safe set. There is a constant $C_{\beta,c}$, independent of $n$ and $A$, such that for all $m\in\mathcal S_{\beta,A}(c)$
--
--   $$
--   \Big\|\mathbf E_{\mathcal D_n}\big[D(m)\big(\widehat Q(m)^2-Q(m)^2\big)D(m)\big]\Big\|_{L^2}\le\frac{C_{\beta,c}}{\sqrt n}.
--   $$
--
--   The event $\Omega_{\beta,c}$ of Corollary 5.9 is stated for $Q$ while the algorithm uses $\widehat Q$; this lemma bounds the difference.
--
--   **Formalization Note** $\mathbf E_{\mathcal D_n}$ is the diagonal part and $\|X\|_{L^2}=\|X\|_F/\sqrt n$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 6.4, p. 38

import Mathlib
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Resolvent

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_6_4 (β c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    ∃ K : ℝ,
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → opNorm A ≤ 3 →
        ∀ m ∈ safeSet β A c,
          schatten2 (diagPart (Dmat m * (Qhat β A m ^ 2 - Qres β A m ^ 2) * Dmat m)) ≤
            K / Real.sqrt n := by sorry

end SKHessianAscent
