-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_exp3_pseudo_regret_anytime
-- name    : RegretBandits.Adversarial.exp3_pseudo_regret_anytime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:02:39.830349+00:00
-- url     : https://prove2.me/theorems/b7691fc7-8e45-4d2d-970f-7cbe70afd974
-- title:
--   Theorem 3.1, Eq. (3.3) — pseudo-regret of anytime Exp3
-- statement:
--   Let $K \ge 2$ and run Exp3 with the time-varying learning rates
--   $$
--   \eta_t = \sqrt{\frac{\ln K}{tK}}, \qquad t = 1, 2, \dots,
--   $$
--   which do not depend on the horizon, against any adaptive adversary with losses in $[0,1]$. Then for every horizon $n \ge 1$,
--   $$
--   \overline R_n \le 2\sqrt{nK\ln K}.
--   $$
--
--   This is the anytime version of Theorem 3.1: the forecaster does not need to know $n$, at the price of the constant $2$ instead of $\sqrt 2$.
--
--   **Formalization Note** The rates are indexed as in the Exp3 box, where $p_{t+1}$ uses $\eta_t$; the value at $t = 0$ is never effective. The run and the adversary are fixed before the horizon $n$ is chosen, so a single run satisfies the bound at every $n$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 24, Theorem 3.1, Eq. (3.3)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Theorem 3.1, eq. (3.3) (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 24). If Exp3 is run with the
anytime learning rates `η_t = √(ln K/(tK))` against any adaptive adversary with losses in `[0,1]`,
then for every horizon `n ≥ 1` the pseudo-regret satisfies `R̄_n ≤ 2 √(n K ln K)`. (The value
`η_0` is never used: it only multiplies `L̃_{·,0} = 0`.) -/
theorem exp3_pseudo_regret_anytime {K : ℕ} (hK : 2 ≤ K) (ℓ : Adversary K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K)
    (hI : IsRun P (exp3Prob (fun t => Real.sqrt (Real.log K / (t * K))) ℓ) I)
    (n : ℕ) (hn : 1 ≤ n) :
    pseudoRegret P ℓ n I ≤ 2 * Real.sqrt (n * K * Real.log K) := by sorry

end RegretBandits.Adversarial
