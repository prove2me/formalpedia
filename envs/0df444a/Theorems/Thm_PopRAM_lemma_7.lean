-- Prove2me | Theorems.Thm_PopRAM_lemma_7
-- name    : PopRAM.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:24:02.433351+00:00
-- url     : https://prove2.me/theorems/6baaeba4-ad1a-4461-902d-549c0987ddbd
-- title:
--   Lemma 7 — Out$(\ell,i)$ creates $2^\ell$ output agents whp in one round
-- statement:
--   For every $C>1$ and $\eta>0$ there are $c$ and $n_0$ such that for every $n\ge n_0$ and every configuration with $m$ marked weight agents $(p_\ell,\mathrm{out}_i)$ and at least $m+(1-1/C)n$ free agents:
--
--   1. with probability at least $1-n^{-\eta}$, within $c\,n\log_2 n$ interactions (one round) no marked agent remains;
--   2. on every schedule and at every time, (number of output agents) + (number of marked agents) and (number of unmarked weight agents) + (number of marked agents) keep their initial values.
--
--   So when no marked agent remains, exactly $m$ new output agents exist and all $m$ weight agents are preserved. With $m=|P_\ell|=2^\ell$ this is Lemma 7.
--
--   **Formalization Note** "Otherwise an Anomaly is signalled" is the check at the next round (Protocol 15, line 9): a marked agent remains.
--
--   Differences from the source:
--   - generalization: the weight P_ℓ of 2^ℓ agents → any number m of marked agents; reason: m = 2^ℓ is an instance
--   - reading: 'Throughout the protocol, at least (1 − 1/C)n agents remain free' → at least m + (1 − 1/C)n free agents initially; reason: the protocol consumes m free agents
--   - reading: 'otherwise an Anomaly is signalled' → the complement of clause 1's event; reason: Protocol 15, line 9, signals exactly when a marked agent remains
--   - encoding: one round → c·n·log₂ n interactions; reason: a round lasts Θ(log n) time
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Lemma 7 and Protocol 15, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_PopRAM_Protocol
import Definitions.Def_PopRAM_OutProtocol

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Lemma 7** with Protocol 15 (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version
sha256 f13223b3…, p.26, PDF p.27). "The protocol Out(ℓ, i) correctly creates a subpopulation of 2^ℓ
agents in state out_i whp in one round, otherwise an Anomaly is signalled."

For every `C > 1` and `η > 0` there are `c` and `n₀` such that for every `n ≥ n₀` and every
configuration with `m` marked weight agents `S` and at least `m + (1 − 1/C)n` free agents:
1. with probability at least `1 − n^{-η}`, within `c·n log₂ n` interactions (one round) no marked
   agent remains;
2. on every schedule and at every time, `#O + #S` and `#P + #S` equal their initial values; so when
   no marked agent remains, exactly `m` new output agents and `m` (unmarked) weight agents exist.

**Formalization Note** The paper's case is `m = |P_ℓ| = 2^ℓ`; the statement holds for every `m`.
"Otherwise an Anomaly is signalled" is the event that a marked agent remains at the end of the round
(Protocol 15, line 9), the complement of clause 1's event. -/
theorem lemma_7 (C : ℝ) (hC : 1 < C) (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c₀ : Fin n → OutState,
      (countIn c₀ (· = OutState.S) : ℝ) + (1 - 1 / C) * n ≤ countIn c₀ (· = OutState.free) →
      sched n {ω | ¬ ∃ t : ℕ, (t : ℝ) ≤ c * n * Real.logb 2 n ∧
          ∀ b, run outδ c₀ ω t b ≠ OutState.S} ≤ whpBound n η ∧
      ∀ ω t,
        countIn (run outδ c₀ ω t) (· = OutState.O) + countIn (run outδ c₀ ω t) (· = OutState.S)
          = countIn c₀ (· = OutState.O) + countIn c₀ (· = OutState.S) ∧
        countIn (run outδ c₀ ω t) (· = OutState.P) + countIn (run outδ c₀ ω t) (· = OutState.S)
          = countIn c₀ (· = OutState.P) + countIn c₀ (· = OutState.S) := by sorry

end PopRAM
