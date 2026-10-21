-- Prove2me | Theorems.Thm_ProxBundle_GPB_proposition_4_9
-- name    : ProxBundle.GPB.proposition_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:33.975277+00:00
-- url     : https://prove2.me/theorems/488519a4-fd1b-4e6b-8fce-488d8ae2582c
-- title:
--   Proposition 4.9, p. 17 — total iteration complexity of every GPB variant
-- statement:
--   Let $f+h$ satisfy the paper's hybrid convex composite assumptions, and let $(M_f,L_f)$ be a nonnegative hybrid pair with $M_f^2+\bar\varepsilon L_f>0$. Let $(\bar M_f,\bar L_f)$ minimize $M^2+\bar\varepsilon L$ among all admissible nonnegative pairs. For every GPB run from $x_0\in D$ with $\lambda,\bar\varepsilon>0$ and $\tau$ specified by (38), there is an iteration $j$ with $\phi(y_j)-\phi^*\le\bar\varepsilon$ and
--   $$
--   j\le\left(\left\lceil\left(1+\frac{8\lambda_\mu(M_f^2+\bar\varepsilon L_f)}{\bar\varepsilon}\right)\max\left\{\log\frac{4\bar t}{\bar\varepsilon},0\right\}\right\rceil+1\right)
--   \left(\operatorname{serBound}(\mu,\lambda,\bar\varepsilon,d_0^2)+1\right).
--   $$
--   Here $d_0=\|x_0-x_0^*\|$, $\lambda_\mu=\lambda/(1+\lambda\mu)$, $\bar t$ is (58), and $\operatorname{serBound}$ is the minimum in (61), with its $\mu=0$ limit. This is an explicit total iteration bound for every admissible BU variant.
--
--   **Formalization Note** The ceiling and maximum correct the printed omission of integer rounding. The positive denominator makes (38) a valid $\tau\in(0,1)$. Functions are real-valued on $D$, and every BU null step retains the paper's existential auxiliary model.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 17, Proposition 4.9, (61)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Proposition 4.9, p. 17: the total GPB iteration bound (61), with the
rounding correction and positive denominator required by (38). -/
theorem proposition_4_9 {n : ℕ} (P : Instance n) (μ Mf Lf Mbar Lbar lam ε : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mf Lf)
    (hpos : 0 < Mf ^ 2 + ε * Lf)
    (hmin : P.IsMinPair ε Mbar Lbar)
    (hx0s : P.IsNearestOpt x0 x0s) (hx0 : x0 ∈ P.D)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hrun : IsRun P μ lam ε (tau38 μ lam ε Mf Lf) x0 R) :
    ∃ j : ℕ, (j : ℝ) ≤
      ((⌈(1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε) *
        max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0⌉ : ℝ) + 1) *
        (serBound μ lam ε (‖x0 - x0s‖ ^ 2) + 1) ∧
      P.φ (R.y j) - P.φ x0s ≤ ε := by sorry

end ProxBundle.GPB
