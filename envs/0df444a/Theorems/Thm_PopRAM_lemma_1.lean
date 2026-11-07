-- Prove2me | Theorems.Thm_PopRAM_lemma_1
-- name    : PopRAM.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:23:27.226069+00:00
-- url     : https://prove2.me/theorems/6aa8867f-8154-4be5-8d34-7b0d5582bf24
-- title:
--   Lemma 1 — the one-way epidemic reaches all agents in $\Theta(\log n)$ time whp
-- statement:
--   For every $\eta>0$ there are constants $c_1,c_2>0$ and $n_0$ such that for every $n\ge n_0$ and every configuration of the one-way epidemic $(x,y)\to(x,\max\{x,y\})$ with exactly one infected agent, the number $T$ of interactions until all agents are infected satisfies
--   $$c_1\,n\log_2 n\le T\le c_2\,n\log_2 n$$
--   with probability at least $1-n^{-\eta}$.
--
--   The epidemic is the dissemination primitive of the phase clock and of the MC+ subroutines PUT$^e$ and GET$^e$.
--
--   Differences from the source:
--   - encoding: Θ(log n) time whp → both c₁·n log₂ n ≤ T and T ≤ c₂·n log₂ n interactions with probability ≥ 1 − n^{−η}; reason: time = interactions / n; Θ states both bounds
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Lemma 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_PopRAM_Protocol
import Definitions.Def_PopRAM_Epidemic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Lemma 1** (Lemma 2 in [AAE08a]) (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held
version sha256 f13223b3…, p.2, PDF p.3). "Starting from a single infected agent, the epidemic
reaches all agents in Θ(log n) time whp."

For every `η > 0` there are `c₁, c₂ > 0` and `n₀` such that for every `n ≥ n₀` and every
configuration of the one-way epidemic with exactly one infected agent, the time `T` until all agents
are infected satisfies `c₁·n log₂ n ≤ T ≤ c₂·n log₂ n` interactions with probability at least
`1 − n^{-η}`.

**Formalization Note** `Θ(log n)` time is `Θ(n log n)` interactions; both the lower and the upper
bound hold whp. -/
theorem lemma_1 (η : ℝ) (hη : 0 < η) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c₀ : Fin n → Bool,
      countIn c₀ (· = true) = 1 →
      sched n {ω | ¬ ∃ t : ℕ, hit epidemicδ c₀ {c | ∀ b, c b = true} ω = t ∧
          c₁ * n * Real.logb 2 n ≤ t ∧ (t : ℝ) ≤ c₂ * n * Real.logb 2 n}
        ≤ whpBound n η := by sorry

end PopRAM
