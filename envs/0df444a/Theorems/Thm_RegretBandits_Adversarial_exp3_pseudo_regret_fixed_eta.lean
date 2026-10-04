-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_exp3_pseudo_regret_fixed_eta
-- name    : RegretBandits.Adversarial.exp3_pseudo_regret_fixed_eta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:02:27.056382+00:00
-- url     : https://prove2.me/theorems/87005f59-f923-4507-95bb-ae0b8a4c7fb0
-- title:
--   Theorem 3.1, Eq. (3.2) — pseudo-regret of Exp3 with a fixed learning rate
-- statement:
--   Let $K \ge 2$ and $n \ge 1$, and run Exp3 with the constant learning rate
--   $$
--   \eta_t = \eta = \sqrt{\frac{2\ln K}{nK}}
--   $$
--   against any adaptive adversary with losses $\ell_{i,t} \in [0,1]$. Then the pseudo-regret $\overline R_n = \mathbb E\sum_{t=1}^n \ell_{I_t,t} - \min_i \mathbb E\sum_{t=1}^n \ell_{i,t}$ satisfies
--   $$
--   \overline R_n \le \sqrt{2nK\ln K}.
--   $$
--
--   This is the basic guarantee of exponential weights with importance-weighted loss estimates under bandit feedback.
--
--   **Formalization Note** The adversary may react to the forecaster's past actions; the oblivious special case (a fixed loss table) is the setting of the published `BanditAlgorithm.adversarial_bandit_exp3_regret_bound`, which states the bound in gains for its own model of Exp3.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 24, Theorem 3.1, Eq. (3.2)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Theorem 3.1, eq. (3.2) (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 24). If Exp3 is run with the
constant learning rate `η_t = η = √(2 ln K/(nK))` against any adaptive adversary with losses in
`[0,1]`, then the pseudo-regret satisfies `R̄_n ≤ √(2 n K ln K)`. -/
theorem exp3_pseudo_regret_fixed_eta {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n)
    (ℓ : Adversary K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K)
    (hI : IsRun P (exp3Prob (fun _ => Real.sqrt (2 * Real.log K / (n * K))) ℓ) I) :
    pseudoRegret P ℓ n I ≤ Real.sqrt (2 * n * K * Real.log K) := by sorry

end RegretBandits.Adversarial
