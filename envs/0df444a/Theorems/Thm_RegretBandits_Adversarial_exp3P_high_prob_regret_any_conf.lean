-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_exp3P_high_prob_regret_any_conf
-- name    : RegretBandits.Adversarial.exp3P_high_prob_regret_any_conf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:02:03.354842+00:00
-- url     : https://prove2.me/theorems/805cfffb-337c-492c-a42b-8fc27b00faf7
-- title:
--   Theorem 3.2, Eq. (3.11) — high-probability regret of Exp3.P at every confidence level
-- statement:
--   Let $K \ge 2$ and $n \ge 1$, and run Exp3.P with the parameters
--   $$
--   \beta = \sqrt{\frac{\ln K}{nK}}, \qquad \eta = 0.95\sqrt{\frac{\ln K}{nK}}, \qquad \gamma = 1.05\sqrt{\frac{K \ln K}{n}},
--   $$
--   which do not depend on any confidence level, against any adaptive adversary with gains in $[0,1]$. Then for every $\delta \in (0,1)$, with probability at least $1-\delta$,
--   $$
--   R_n \le \sqrt{\frac{nK}{\ln K}}\, \ln(\delta^{-1}) + 5.15\sqrt{nK \ln K}.
--   $$
--
--   Because one run of the algorithm satisfies the bound at every confidence level simultaneously, the tail of $R_n$ can be integrated, which gives the expected-regret bound of Theorem 3.3.
--
--   **Formalization Note** As for (3.10), the statement is asserted for every $n \ge 1$; where $\gamma > 1$ the rule can have negative entries (and then no run exists), and in that range the printed bound already follows from $R_n \le n$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 30, Theorem 3.2, Eq. (3.11)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3P

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Theorem 3.2, eq. (3.11) (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 30). If Exp3.P is run with
`β = √(ln K/(nK))`, `η = 0.95 √(ln K/(nK))`, `γ = 1.05 √(K ln K/n)` (parameters that do not
depend on `δ`) against any adaptive adversary with gains in `[0,1]`, then for every `δ ∈ (0,1)`,
with probability at least `1 - δ`, `R_n ≤ √(nK/ln K) ln(δ⁻¹) + 5.15 √(n K ln K)`. -/
theorem exp3P_high_prob_regret_any_conf {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n)
    (g : Adversary K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K)
    (hI : IsRun P
      (exp3PProb (Real.sqrt (Real.log K / (n * K)))
        (1.05 * Real.sqrt (K * Real.log K / n))
        (0.95 * Real.sqrt (Real.log K / (n * K))) g) I)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | regret g n I ω ≤
        Real.sqrt (n * K / Real.log K) * Real.log δ⁻¹ + 5.15 * Real.sqrt (n * K * Real.log K)} := by sorry

end RegretBandits.Adversarial
