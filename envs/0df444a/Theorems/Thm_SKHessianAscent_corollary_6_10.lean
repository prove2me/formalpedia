-- Prove2me | Theorems.Thm_SKHessianAscent_corollary_6_10
-- name    : SKHessianAscent.corollary_6_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:21:02.242258+00:00
-- url     : https://prove2.me/theorems/f5749b74-4901-4271-b1f7-adf166e96fcf
-- title:
--   Corollary 6.10, desiderata (d3)–(d5) — drift error and Lipschitz bounds for $\widehat Q$, the ASL drift and the Jarzynski integrand on the safe set
-- statement:
--   Fix $0<\beta<1$, $c>0$ and a constant $C>0$. Let $\Omega_{\beta,c}$ be the event (6.5): for every diagonal $D\succeq I_n$ with $\beta^2\mathrm{tr}_n(D^{-1})I_n-\beta A+D\succeq cI_n$,
--   $$\Big\|\mathbf E_{\mathcal D_n}\big[D(\beta^2\mathrm{tr}_n(D^{-1})I_n-\beta A+D)^{-2}D\big]-\frac{I_n}{1-\beta^2\mathrm{tr}_n(D^{-2})}\Big\|_{L^2}\le\frac{C\beta}{\gamma_Y^2\sqrt n},\qquad \gamma_Y=\min\Big\{\frac{(1-\beta)^4}{4(1+2\beta^2)^2},\Big(1+\frac{1+3\beta}{c}\Big)^{-2}\Big\}.$$
--
--   There is a constant $K=K(\beta,c,C)$, independent of $n$ and $A$, such that for every $n$ and every symmetric $A$ in the events $\{\|A\|_{\mathrm{op}}\le3\}$ and $\Omega_{\beta,c}$, the following hold for all $m,w\in\mathcal S_{\beta,A}(c)$:
--
--   1. **(d3)** $\ \|f(m)-m\|_2\le K$;
--   2. **(d4a)** $\ \|\widehat Q(m)-\widehat Q(w)\|_F\le K\|m-w\|_2$;
--   3. **(d4b)** $\ \big\|\widehat Q(m)(m-f(m))-\widehat Q(w)(w-f(w))\big\|_2\le K\|m-w\|_2$;
--   4. **(d5)** $\ |\omega(m)-\omega(w)|\le K\|m-w\|_2$,
--
--   where $f$ is the drift correction (2.4) and $\omega(m)=\tfrac12(\mathrm{Tr}[\widehat Q(m)]+\|m\|_2^2)$.
--
--   These are the regularity properties of the coefficients of the algorithmic localization process and of its Jarzynski weights; because the safe set is not convex, they cannot be obtained by integrating derivative bounds along segments.
--
--   **Formalization Note** The paper's constants $\varepsilon_{\mathrm{drift}}$, $L$, $L_{\mathrm{drift}}$, $L_\omega$ are bounded by one constant $K$. The universal constant in the definition of $\Omega_{\beta,c}$ is the parameter $C$, and $K$ may depend on it.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Corollary 6.10, p. 41; desiderata (d3)–(d5), pp. 5–6; events (6.3)–(6.5), p. 37

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem corollary_6_10 (β c C : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (hC : 0 < C) :
    ∃ K : ℝ,
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → opNorm A ≤ 3 →
        A ∈ OmegaEvent β c C n →
          (∀ m ∈ safeSet β A c, l2 (fDrift β A m - m) ≤ K) ∧
          (∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
            frob (Qhat β A m - Qhat β A w) ≤ K * l2 (m - w)) ∧
          (∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
            l2 ((Qhat β A m).mulVec (m - fDrift β A m) - (Qhat β A w).mulVec (w - fDrift β A w)) ≤
              K * l2 (m - w)) ∧
          (∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
            |omega β A m - omega β A w| ≤ K * l2 (m - w)) := by sorry

end SKHessianAscent
