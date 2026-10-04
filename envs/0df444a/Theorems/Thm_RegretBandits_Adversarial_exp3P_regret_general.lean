-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_exp3P_regret_general
-- name    : RegretBandits.Adversarial.exp3P_regret_general
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:01:48.472206+00:00
-- url     : https://prove2.me/theorems/759b5a4a-d115-47f3-8c78-c6b2f5843315
-- title:
--   Eq. (3.12) — high-probability regret of Exp3.P for general parameters
-- statement:
--   Let $K \ge 2$, $n \ge 1$, and consider any adaptive adversary with gains in $[0,1]$. Run Exp3.P with parameters $\beta \in (0,1]$, $\eta > 0$ and $\gamma$ satisfying
--   $$
--   \gamma \le \tfrac12, \qquad (1+\beta) K \eta \le \gamma .
--   $$
--   Then for every $\delta \in (0,1)$, with probability at least $1-\delta$, the regret $R_n = \max_i \sum_{t=1}^n g_{i,t} - \sum_{t=1}^n g_{I_t,t}$ satisfies
--   $$
--   R_n \le \beta n K + \gamma n + (1+\beta)\eta K n + \frac{\ln(K\delta^{-1})}{\beta} + \frac{\ln K}{\eta}.
--   $$
--
--   This is the general bound proved in the course of Theorem 3.2; the tuned bounds (3.10) and (3.11) follow by substituting the parameters.
--
--   **Formalization Note** The book's Exp3.P has $\beta \in [0,1]$ and $\eta > 0$; strict $\beta > 0$ is needed because the bound divides by $\beta$. The hypotheses force $\gamma > 0$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 30, Eq. (3.12) (proof of Theorem 3.2)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3P

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Eq. (3.12) (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 30, proof of Theorem 3.2). If Exp3.P is
run with `0 < β ≤ 1`, `η > 0`, `γ ≤ 1/2` and `(1 + β) K η ≤ γ` against any adaptive adversary
with gains in `[0,1]`, then for every `δ ∈ (0,1)`, with probability at least `1 - δ`,
`R_n ≤ β n K + γ n + (1 + β) η K n + ln(K δ⁻¹) / β + ln K / η`. -/
theorem exp3P_regret_general {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n) (g : Adversary K)
    (β γ η δ : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hη : 0 < η) (hγ : γ ≤ 1 / 2)
    (hβηγ : (1 + β) * K * η ≤ γ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K) (hI : IsRun P (exp3PProb β γ η g) I) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | regret g n I ω ≤
        β * n * K + γ * n + (1 + β) * η * K * n + Real.log (K * δ⁻¹) / β + Real.log K / η} := by sorry

end RegretBandits.Adversarial
