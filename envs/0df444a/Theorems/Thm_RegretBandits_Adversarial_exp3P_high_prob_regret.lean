-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_exp3P_high_prob_regret
-- name    : RegretBandits.Adversarial.exp3P_high_prob_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:01:54.403325+00:00
-- url     : https://prove2.me/theorems/f25938d6-b2fc-45b4-a491-9448218c4241
-- title:
--   Theorem 3.2, Eq. (3.10) — high-probability regret of Exp3.P tuned to δ
-- statement:
--   Let $K \ge 2$ arms, a horizon $n \ge 1$ and a confidence level $\delta \in (0,1)$ be given, and run Exp3.P with
--   $$
--   \beta = \sqrt{\frac{\ln(K\delta^{-1})}{nK}}, \qquad \eta = 0.95\sqrt{\frac{\ln K}{nK}}, \qquad \gamma = 1.05\sqrt{\frac{K \ln K}{n}}
--   $$
--   against any adaptive adversary with gains in $[0,1]$. Then, with probability at least $1-\delta$,
--   $$
--   R_n \le 5.15 \sqrt{nK \ln(K\delta^{-1})}.
--   $$
--
--   This is the first high-probability bound of Theorem 3.2, for the version of Exp3.P that takes $\delta$ as an input.
--
--   **Formalization Note** The statement holds for every $n \ge 1$; the book's proof notes that the bound is trivial when $n \le 5.15\sqrt{nK\ln(K\delta^{-1})}$ because $R_n \le n$ (the page says "$n \ge$", a misprint). In that trivial range $\gamma$ may exceed $1$; then Exp3.P's vector can have negative entries (and then no run exists), but in either case the printed bound is already implied by $R_n \le n$ there. Outside it, $\gamma \le 0.21$ and $\beta \le 0.1$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, pp. 29–30, Theorem 3.2, Eq. (3.10)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3P

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Theorem 3.2, eq. (3.10) (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, pp. 29–30). For any
`δ ∈ (0,1)`, if Exp3.P is run with `β = √(ln(K δ⁻¹)/(nK))`, `η = 0.95 √(ln K/(nK))`,
`γ = 1.05 √(K ln K/n)` against any adaptive adversary with gains in `[0,1]`, then with probability
at least `1 - δ`, `R_n ≤ 5.15 √(n K ln(K δ⁻¹))`. -/
theorem exp3P_high_prob_regret {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n) (g : Adversary K)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K)
    (hI : IsRun P
      (exp3PProb (Real.sqrt (Real.log (K * δ⁻¹) / (n * K)))
        (1.05 * Real.sqrt (K * Real.log K / n))
        (0.95 * Real.sqrt (Real.log K / (n * K))) g) I) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | regret g n I ω ≤ 5.15 * Real.sqrt (n * K * Real.log (K * δ⁻¹))} := by sorry

end RegretBandits.Adversarial
