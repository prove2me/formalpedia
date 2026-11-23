-- Prove2me | Theorems.Thm_TIESharp_lemma_5_6_seven_endpoint_improvement
-- name    : TIESharp.lemma_5_6_seven_endpoint_improvement
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:20.962163+00:00
-- url     : https://prove2.me/theorems/a5dda76f-d62e-4f30-ae1f-71ebd885f3b6
-- title:
--   Lemma 5.6 — endpoint improvement of the mean-load estimate
-- statement:
--   Let $T>0$, $n=7$, and $0<\lambda_i\le\mu_i/T$ satisfy Lemma 5.3 and $\bar d=d/(2T)$. At either spoke endpoint, $\theta_0\le d_0-1/3$ or $\theta_7\le1-d_7$. If
--   $$\frac{\lambda_i}T-d_i>\frac13,\qquad \frac{\mu_i}{T\lambda_i}>\frac34,$$
--   then
--   $$\theta_i\lambda_i(\mu_i-2Td_i)\le
--   \frac T2\left(\frac{\sqrt{i+1}+1}{7}-2d_i\right)-2T.$$
--   Here the printed $\sqrt{i+1}$ is indexed by the Lean value $i.val+1$; in the statement's `Fin 7` expression `Real.sqrt i.1 + 1` denotes $\sqrt{i}+1$ under the zero-based representation used for the first endpoint, and the second endpoint is obtained by symmetry.
--
--   The one-dimensional proof minimizes over the dominance-frontier patch for $(a,b)=(\lambda_i/T-d_i,\mu_i/(T\lambda_i))$, using concavity and the endpoint slopes.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Lemma 5.6, p.27; equations (5.4) and (5.6), p.28.

import Mathlib
import Definitions.Def_TIESharp_selectorConstraints

set_option autoImplicit false

/-- For seven machines, a spoke endpoint improves the two-spoke mean bound over a
single-coordinate neighborhood of the optimum (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Lemma 5.6, p.27). -/
theorem TIESharp.lemma_5_6_seven_endpoint_improvement (T : ℝ) (hT : 0 < T)
    (lambda mu d : Fin 7 → ℝ) (hdd : ∀ i, 0 < d i)
    (hbound : ∀ i, 0 ≤ lambda i ∧ lambda i ≤ d i ∧ T * d i ≤ mu i ∧ mu i ≤ T * lambda i) :
    ∀ theta : Fin 7 → ℝ, TIESharp.selectorConstraints d theta →
      ∀ i : Fin 7, 1 / 3 < lambda i / T - d i ∧ 3 / 4 < mu i / (T * lambda i) →
        theta i * lambda i * (mu i - 2 * T * d i) ≤
          T / 2 * (((Real.sqrt i.1 + 1) / 7 - 2 * (lambda i / T - d i))) - 2 * T := by sorry
