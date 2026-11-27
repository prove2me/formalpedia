-- Prove2me | Theorems.Thm_ProxBundle_GPB_Supplement_theorem_3_1
-- name    : ProxBundle.GPB.Supplement.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:34:51.639733+00:00
-- url     : https://prove2.me/theorems/c320b511-6ce9-4420-b8d0-0cebeb5a57fc
-- title:
--   Theorem 3.1 — full uniform GPB rate over (37)
-- statement:
--   Fix $C>0$ before all instance and run parameters. Let $f+h$ satisfy (A1)–(A3) on $\mathbb R^n$ with nonnegative parameters $M_f,L_f,\mu$. Choose the minimizing pair $(\bar M_f,\bar L_f)$ from (9), an initial $x_0\in D$, and a nearest optimum $x_0^*$, and put $r=\|x_0-x_0^*\|^2$, $S=M_f^2+\varepsilon L_f>0$. For every $\varepsilon,\lambda>0$ satisfying the entire interval $\varepsilon/(CS)\le\lambda\le Cr/\varepsilon$, every GPB variant with $\tau$ given by (38) has an index $j$ such that
--
--   $$
--   \phi(y_j)-\phi^*\le\varepsilon,\qquad
--   j\le10(1+2\max\{C,1\})(L+1)(B_\mu(\varepsilon,S,r)+1).
--   $$
--   Here $B_\mu$ is the two-regime rate (5), with its convex-case convention, $\bar t$ is exactly (58) for the minimizing pair, and $L=\max\{\log(4\bar t/\varepsilon),0\}$ when $\bar t>0$, otherwise zero. This companion theorem gives a uniform simplified rate across the full admissible stepsize interval and every BU variant.
--
--   **Formalization Note** The published domain-relative model and its omitted lower semicontinuity of $f$ and of the auxiliary BU model are retained; all comparisons occur on $D$. The coefficient (38) uses the given pair $(M_f,L_f)$, whereas $\bar t$ uses the minimizing pair. The constant depends only on $C$. The interval's positive denominator, the $\mu=0$ branch, and the zero logarithmic factor convention are explicit.
--
--   Differences from the source:
--   - generalization: The source assumes lower semicontinuity of f and uses an oracle on its extended domain. → The published domain-relative model retains the oracle inequality only on D and omits lower semicontinuity of f.; reason: Every oracle comparison in these results lies in D; the omitted regularity is not used. The immutable model is reused.
--   - encoding: Theorem 3.1 gives the uniform rate (5) up to a logarithmic term. → The bound is K31(C)(L+1)(B_mu(epsilon,S,r)+1), with C quantified before all problem data.; reason: The scalar comparisons from (61)–(66) give K31(C)=10(1+2max(C,1)); no per-instance constant is allowed.
--   - reading: The interval (37) and coefficient (38) divide by S=Mf²+epsilon Lf. → StepInterval explicitly requires S>0.; reason: S=0 leaves the printed input formulas undefined; no defined input is removed. The mu=0 and tbar=0 limits are explicit.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 11, Theorem 3.1, (37)–(38); pp. 18–19, proof (62)–(66); p. 2, (5)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Definitions.Def_ProxBundle_GPB_Supplement_Rates

namespace ProxBundle.GPB.Supplement

/-- Theorem 3.1: the full interval and both regimes, with one explicit logarithmic
factor and a constant depending only on the fixed universal input C. -/
theorem theorem_3_1 (C : ℝ) (hC : 0 < C)
    {n : ℕ} (P : Instance n) (μ Mf Lf Mbar Lbar lam ε : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mf Lf)
    (hmin : P.IsMinPair ε Mbar Lbar)
    (hx0s : P.IsNearestOpt x0 x0s) (hx0 : x0 ∈ P.D)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hinterval : StepInterval C ε (Mf ^ 2 + ε * Lf) lam (‖x0 - x0s‖ ^ 2))
    (hrun : IsRun P μ lam ε (tau38 μ lam ε Mf Lf) x0 R) :
    Obtains P R x0s ε
      (K31 C * (logFactor (tbar Mbar Lbar lam ‖x0 - x0s‖) ε + 1) *
        (rate μ ε (Mf ^ 2 + ε * Lf) (‖x0 - x0s‖ ^ 2) + 1)) := by sorry

end ProxBundle.GPB.Supplement
