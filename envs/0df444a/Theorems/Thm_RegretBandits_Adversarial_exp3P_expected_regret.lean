-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_exp3P_expected_regret
-- name    : RegretBandits.Adversarial.exp3P_expected_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:02:12.445284+00:00
-- url     : https://prove2.me/theorems/c51e71ae-fcf0-4655-ad94-38654ea59c52
-- title:
--   Theorem 3.3 — expected regret of Exp3.P against adaptive adversaries
-- statement:
--   Let $K \ge 2$ arms and a horizon $n \ge 1$ be given, and run Exp3.P with
--   $$
--   \beta = \sqrt{\frac{\ln K}{nK}}, \qquad \eta = 0.95\sqrt{\frac{\ln K}{nK}}, \qquad \gamma = 1.05\sqrt{\frac{K \ln K}{n}}
--   $$
--   against any adaptive adversary, whose gains $g_{i,t} \in [0,1]$ may depend on the forecaster's past actions. Then the expected regret satisfies
--   $$
--   \mathbb E\, R_n \le 5.15\sqrt{nK\ln K} + \sqrt{\frac{nK}{\ln K}},
--   $$
--   where $R_n = \max_{i} \sum_{t=1}^n g_{i,t} - \sum_{t=1}^n g_{I_t,t}$ is the regret, with the maximum inside the expectation.
--
--   Against a non-oblivious adversary, a bound on the pseudo-regret does not bound the expected regret; this theorem gives an $O(\sqrt{nK\ln K})$ bound on the expected regret itself, matching the lower bound $\sqrt{nK}/20$ of Theorem 3.4 up to a logarithmic factor.
--
--   **Formalization Note** The expectation is the integral of the regret under the law of the run; the regret is bounded by $n$ and measurable, so the integral is not a default value. The statement is asserted for every $n \ge 1$. When $1.05\sqrt{K\ln K/n} > 1$ the rule can have negative entries (and then no run exists), and in that range the bound already follows from $R_n \le n$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 32, Theorem 3.3, Eq. (3.17)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3P

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Theorem 3.3 (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 32), expected regret of Exp3.P. If
Exp3.P is run with `β = √(ln K/(nK))`, `η = 0.95 √(ln K/(nK))`, `γ = 1.05 √(K ln K/n)` against any
adaptive adversary with gains in `[0,1]`, then
`E R_n ≤ 5.15 √(n K ln K) + √(nK/ln K)`, eq. (3.17), where `R_n` is the regret (maximum inside
the expectation). -/
theorem exp3P_expected_regret {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n) (g : Adversary K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K)
    (hI : IsRun P
      (exp3PProb (Real.sqrt (Real.log K / (n * K)))
        (1.05 * Real.sqrt (K * Real.log K / n))
        (0.95 * Real.sqrt (Real.log K / (n * K))) g) I) :
    ∫ ω, regret g n I ω ∂P ≤
      5.15 * Real.sqrt (n * K * Real.log K) + Real.sqrt (n * K / Real.log K) := by sorry

end RegretBandits.Adversarial
