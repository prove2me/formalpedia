-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_6_5
-- name    : SKHessianAscent.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:18:50.971816+00:00
-- url     : https://prove2.me/theorems/393ea4d1-6494-4b84-89f4-9f370b59602c
-- title:
--   Lemma 6.5 — basic properties of $\delta_{\mathrm{diag}}$ on the good set: bounded in operator norm and $C_{\beta,c}/\sqrt n$-Lipschitz in $\|\cdot\|_{L^2}$
-- statement:
--   Fix $0<\beta<1$ and $c>0$, and let $A$ be a symmetric real $n\times n$ matrix with $\|A\|_{\mathrm{op}}\le3$. Write $D=D(m)=\mathrm{diag}(1/(1-m_i^2))$, $a(m)=\beta^2\mathrm{tr}_n(D(m)^{-1})$, $Q(m)=(a(m)I_n-\beta A+D(m))^{-1}$ and $\widehat Q(m)=(a(m)I_n-\beta A+D(m)-\tfrac{2\beta^2}{n}mm^{\mathsf T})^{-1}$, and let $\mathcal S_{\beta,A}(c)$ be the safe set. Let
--
--   $$
--   \delta_{\mathrm{diag}}(m)=\mathbf E_{\mathcal D_n}\big[\widehat Q(m)^2\big]D(m)^2-\big(1+\beta^2\mathrm{tr}_n(\widehat Q(m)^2)\big)I_n .
--   $$
--
--   There is a constant $C_{\beta,c}$, independent of $n$ and $A$, such that for all $m,w\in\mathcal S_{\beta,A}(c)$:
--
--   1. $\|\delta_{\mathrm{diag}}(m)\|_{\mathrm{op}}\le C_{\beta,c}$;
--   2. $\|\delta_{\mathrm{diag}}(m)-\delta_{\mathrm{diag}}(w)\|_{L^2}\le\dfrac{C_{\beta,c}}{\sqrt n}\|m-w\|_2$.
--
--   $\delta_{\mathrm{diag}}$ measures how far the drift correction $f$ is from the identity: $f(m)=(I_n+\delta_{\mathrm{diag}}(m)-\tfrac{2\beta^2}{n}\widehat Q(m)^2)m$.
--
--   **Formalization Note** One constant bounds both quantities.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 6.5, eqs. (6.8)–(6.9), p. 38

import Mathlib
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Resolvent

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_6_5 (β c : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    ∃ K : ℝ,
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → opNorm A ≤ 3 →
        ∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
          opNorm (deltaDiag β A m) ≤ K ∧
          schatten2 (deltaDiag β A m - deltaDiag β A w) ≤ K / Real.sqrt n * l2 (m - w) := by sorry

end SKHessianAscent
