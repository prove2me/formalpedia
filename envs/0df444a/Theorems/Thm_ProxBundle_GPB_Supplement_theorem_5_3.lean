-- Prove2me | Theorems.Thm_ProxBundle_GPB_Supplement_theorem_5_3
-- name    : ProxBundle.GPB.Supplement.theorem_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:36:12.08281+00:00
-- url     : https://prove2.me/theorems/351d34d0-bab8-4d97-867e-63bb42754637
-- title:
--   Theorem 5.3 (corrected: integer and small-log boundaries) — adaptive complexity and full uniform rate
-- statement:
--   Fix any $C>0$ before all instance and run data. Let $f+h$ satisfy (A1)–(A3) with nonnegative $M_f,L_f,\mu$, choose its minimizing pair $(\bar M_f,\bar L_f)$, and set $T_\varepsilon^2=\bar M_f^2+\varepsilon\bar L_f$. Start at $x_0\in D$, let $x_0^*$ be a nearest optimum, put $d_0=\|x_0-x_0^*\|$, and take any $\lambda,\varepsilon>0$ and $\beta\ge1$. Every operational 1C-APB run has an accepted index $j$ with $\phi(y_j)-\phi^*\le\varepsilon$ and
--
--   $$
--   j\le\left(\left\lceil2\left(1+\frac{8\lambda_\mu T_\varepsilon^2}{\varepsilon}\right)L\right\rceil+1\right)
--   \left(\operatorname{serBound}(\mu,\lambda,\varepsilon,d_0^2)+1\right).
--   $$
--   In addition, if the full interval (39) holds, namely $T_\varepsilon^2>0$ and $\varepsilon/(CT_\varepsilon^2)\le\lambda\le Cd_0^2/\varepsilon$, there is a successful accepted index satisfying
--
--   $$
--   j\le18(1+2\max\{C,1\})(L+1)(B_\mu(\varepsilon,T_\varepsilon^2,d_0^2)+1).
--   $$
--   Here $\lambda_\mu=\lambda/(1+\lambda\mu)$, $\bar t$ is (58), $L=\max\{\log(4\bar t/\varepsilon),0\}$ for $\bar t>0$ and zero otherwise. The serious-iteration factor has the explicit $\mu=0$ branch from the published model. This companion theorem includes both the arbitrary-stepsize product and the uniform two-regime consequence (16).
--
--   **Formalization Note** The ceiling and positive-part logarithm correct the boundary omission in printed (70); the factor 2, constant 8, and exact $\bar t$ are preserved. The quadratic counterexample and cycle-recurrence justification are retained for moderation. The first clause permits $T_\varepsilon^2=0$, $\mu=0$, every $\beta\ge1$, and initially successful $j=0$; (39) belongs only to the second clause. The count is of accepted iterations, excluding rejected trial evaluations. The published domain-relative model and omitted lower semicontinuity of $f$ are retained.
--
--   Differences from the source:
--   - generalization: The source assumes lower semicontinuity of f and uses an oracle on its extended domain. → The published domain-relative model retains the oracle inequality only on D and omits lower semicontinuity of f.; reason: Every oracle comparison in these results lies in D; the omitted regularity is not used. The immutable model is reused.
--   - correction: The first factor of printed (70) is 2(1+8lambda_mu T_epsilon²/epsilon) log(4tbar/epsilon)+1. → It is ceil(2(1+8lambda_mu T_epsilon²/epsilon)L)+1, with L the positive-part logarithm, zero at tbar=0.; reason: The p.20 cycle recurrence supports this integer bound; literal (70) is negative on the quadratic example in DISPROOF.md. No input cases are excluded.
--   - encoding: The second conclusion gives the uniform rate (16) under (39). → For every fixed C>0 it also gives K53(C)(L+1)(B_mu(epsilon,T_epsilon²,r)+1) under the full interval (39).; reason: The comparison yields K53(C)=18(1+2max(C,1)); the first clause does not assume that interval.
--   - reading: The formulas divide by mu, T_epsilon², and tbar inside a logarithm. → The mu=0 and tbar=0 conventions and continuous threshold are explicit; T_epsilon²>0 is needed only for the interval (39).; reason: This preserves every defined interval input and all arbitrary-stepsize inputs, including T_epsilon²=0.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 21, Theorem 5.3, (70), proof; p. 20, cycle recurrence in Proposition 5.2(b); p. 11, (39); p. 6, (16)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Definitions.Def_ProxBundle_GPB_Supplement_Rates
import Definitions.Def_ProxBundle_GPB_Supplement_Adaptive

namespace ProxBundle.GPB.Supplement

/-- Theorem 5.3 (corrected integer/small-log convention): arbitrary stepsizes,
then the full (39)/(16) consequence. Every beta >= 1 and T²=0 are allowed. -/
theorem theorem_5_3 (C : ℝ) (hC : 0 < C)
    {n : ℕ} (P : Instance n) (μ Mf Lf Mbar Lbar lam ε β : ℝ)
    (x0 x0s : E n) (A : APBRun n)
    (hμ : 0 ≤ μ) (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mf Lf)
    (hmin : P.IsMinPair ε Mbar Lbar)
    (hx0s : P.IsNearestOpt x0 x0s) (hx0 : x0 ∈ P.D)
    (hlam : 0 < lam) (hε : 0 < ε) (hβ : 1 ≤ β)
    (hrun : IsAPBRun P lam ε β x0 A) :
    Obtains P A.accepted x0s ε (adaptiveBound μ lam ε Mbar Lbar ‖x0 - x0s‖) ∧
    (StepInterval C ε (Mbar ^ 2 + ε * Lbar) lam (‖x0 - x0s‖ ^ 2) →
      Obtains P A.accepted x0s ε
        (K53 C * (logFactor (tbar Mbar Lbar lam ‖x0 - x0s‖) ε + 1) *
          (rate μ ε (Mbar ^ 2 + ε * Lbar) (‖x0 - x0s‖ ^ 2) + 1))) := by sorry

end ProxBundle.GPB.Supplement
