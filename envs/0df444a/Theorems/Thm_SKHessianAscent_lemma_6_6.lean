-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_6_6
-- name    : SKHessianAscent.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:19:32.887364+00:00
-- url     : https://prove2.me/theorems/b9ecc64e-3d47-4068-a3c1-81d1a41dbb3f
-- title:
--   Lemma 6.6 — uniform diagonal control: $\|\delta_{\mathrm{diag}}(m)\|_{L^2}\le C_{\beta,c}/\sqrt n$ on the event $\Omega_{\beta,c}$
-- statement:
--   Fix $0<\beta<1$ and $c>0$, and let $A$ be a symmetric real $n\times n$ matrix with $\|A\|_{\mathrm{op}}\le3$. Write $D=D(m)=\mathrm{diag}(1/(1-m_i^2))$, $a(m)=\beta^2\mathrm{tr}_n(D(m)^{-1})$, $Q(m)=(a(m)I_n-\beta A+D(m))^{-1}$ and $\widehat Q(m)=(a(m)I_n-\beta A+D(m)-\tfrac{2\beta^2}{n}mm^{\mathsf T})^{-1}$, and let $\mathcal S_{\beta,A}(c)$ be the safe set. Assume in addition that $A$ lies in the event $\Omega_{\beta,c}$ of (6.5), with universal constant $C$. There is a constant $K=K(\beta,c,C)$, independent of $n$ and $A$, such that for every $m\in\mathcal S_{\beta,A}(c)$
--
--   $$
--   \|\delta_{\mathrm{diag}}(m)\|_{L^2}\le\frac{K}{\sqrt n}.
--   $$
--
--   The same bound, with every $\widehat Q$ replaced by $Q$, holds for all $m\in(-1,1)^n$ such that $D(m)\in S_D$, where $S_D=\{D\in\mathcal D_n([1,\infty)):\beta^2\mathrm{tr}_n(D^{-1})I_n-\beta A+D\succeq cI_n\}$.
--
--   This upgrades the $O(1)$ operator-norm bound of Lemma 6.5 to an $O(n^{-1/2})$ bound in normalized Schatten norm, using the free-probability estimate of Corollary 5.9.
--
--   **Formalization Note** The universal constant in $\Omega_{\beta,c}$ is the parameter $C$ of `OmegaEvent`; $K$ may depend on it.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 6.6, eq. (6.10), p. 39; event (6.5), p. 37

import Mathlib
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Resolvent

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_6_6 (β c C : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (hC : 0 < C) :
    ∃ K : ℝ,
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → opNorm A ≤ 3 →
        A ∈ OmegaEvent β c C n →
          (∀ m ∈ safeSet β A c, schatten2 (deltaDiag β A m) ≤ K / Real.sqrt n) ∧
          (∀ m ∈ cube n, (fun i => (1 - m i ^ 2)⁻¹) ∈ SD β A c →
            schatten2 (deltaDiagRes β A m) ≤ K / Real.sqrt n) := by sorry

end SKHessianAscent
