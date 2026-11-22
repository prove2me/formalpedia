-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_6_7
-- name    : SKHessianAscent.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:20:03.078029+00:00
-- url     : https://prove2.me/theorems/aced6df5-da63-4d62-a4dd-6d26645ad10d
-- title:
--   Lemma 6.7 — closeness of ASL-TAP and PHD: $\|f\|_{\mathrm{Lip}}$, $\|m-f(m)\|_2$, $\|\widehat Q(m)(m-f(m))\|_2$ and its Lipschitz constant are $O(1)$
-- statement:
--   Fix $0<\beta<1$ and $c>0$, and let $A$ be a symmetric real $n\times n$ matrix with $\|A\|_{\mathrm{op}}\le3$. Write $D=D(m)=\mathrm{diag}(1/(1-m_i^2))$, $a(m)=\beta^2\mathrm{tr}_n(D(m)^{-1})$, $Q(m)=(a(m)I_n-\beta A+D(m))^{-1}$ and $\widehat Q(m)=(a(m)I_n-\beta A+D(m)-\tfrac{2\beta^2}{n}mm^{\mathsf T})^{-1}$, and let $\mathcal S_{\beta,A}(c)$ be the safe set. Assume in addition that $A$ lies in the event $\Omega_{\beta,c}$ of (6.5), with universal constant $C$, and let $f$ be the drift correction (6.2). There is a constant $K=K(\beta,c,C)$, independent of $n$ and $A$, such that for all $m,w\in\mathcal S_{\beta,A}(c)$, in Euclidean norm:
--
--   1. $\|f(m)-f(w)\|_2\le K\|m-w\|_2$;
--   2. $\|m-f(m)\|_2\le K$;
--   3. $\|\widehat Q(m)(m-f(m))\|_2\le K$;
--   4. $\|D(m)\widehat Q(m)(m-f(m))\|_2\le K$;
--   5. $\big\|\widehat Q(m)(m-f(m))-\widehat Q(w)(w-f(w))\big\|_2\le K\|m-w\|_2$.
--
--   The two algorithmic processes ASL-TAP and PHD differ by the drift $\widehat Q(m)(m-f(m))$; the lemma shows this drift is bounded and Lipschitz with constants independent of $n$.
--
--   **Formalization Note** Lipschitz norms on the non-convex safe set are two-point inequalities. One constant bounds the five quantities.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 6.7, eqs. (6.11)–(6.14), p. 39

import Mathlib
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Resolvent

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_6_7 (β c C : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (hC : 0 < C) :
    ∃ K : ℝ,
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → opNorm A ≤ 3 →
        A ∈ OmegaEvent β c C n →
          ∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
            l2 (fDrift β A m - fDrift β A w) ≤ K * l2 (m - w) ∧
            l2 (m - fDrift β A m) ≤ K ∧
            l2 ((Qhat β A m).mulVec (m - fDrift β A m)) ≤ K ∧
            l2 ((Dmat m * Qhat β A m).mulVec (m - fDrift β A m)) ≤ K ∧
            l2 ((Qhat β A m).mulVec (m - fDrift β A m) - (Qhat β A w).mulVec (w - fDrift β A w)) ≤
              K * l2 (m - w) := by sorry

end SKHessianAscent
