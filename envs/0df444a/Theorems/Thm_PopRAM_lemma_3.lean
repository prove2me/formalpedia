-- Prove2me | Theorems.Thm_PopRAM_lemma_3
-- name    : PopRAM.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:23:36.739194+00:00
-- url     : https://prove2.me/theorems/a5e0c195-ec8f-4e78-bb16-d5133a2a8141
-- title:
--   Lemma 3 — WeightCreation$(w)$ creates $P_0,\dots,P_{w-2}$ whp in one round, with $\Theta(w^2)$ states
-- statement:
--   1. For every $C>1$, $a>0$ and $\eta>0$ there are $c$ and $n_0$ such that for every $n\ge n_0$, every $w$ with $3\le w\le a\log_2 n$, and every configuration in which exactly one agent is the undelegated leader $\ell_0$, every other agent is free or inert, and at least $2^{w-1}+(1-1/C)n$ agents are free:
--      - with probability at least $1-n^{-\eta}$, within $c\,n\log_2 n$ interactions (one round) the configuration has no anomaly condition: the leader has delegated and no agent is in $p^*(\cdot)$ or in $p_k(i)$ with $i>0$;
--      - on every schedule, whenever this holds, for every $k\le w-2$ exactly $2^k$ agents are in $p_k(0)$ (the weight $P_k$), and the configuration is silent.
--   2. The weight states number $\Theta(w^2)$: there are $c_1,c_2>0$ with $c_1w^2\le|\{p^*(k)\}\cup\{p_k(i)\}|\le c_2w^2$ for all $w\ge3$.
--
--   The weights $P_0,\dots,P_{w-2}$ represent, by unions, every value below $2^{w-1}$; they drive the MC+ input and output conversions.
--
--   **Formalization Note** "Signals an Anomaly otherwise" refers to the check at the next round (p.21), whose condition is the complement of the event in the first bullet.
--
--   Differences from the source:
--   - reading: 'In its first interaction with a free agent, the leader delegates' → the delegation rule in both orientations; rules (1)–(3) initiator first; reason: the delegation is stated for any interaction; the proof counts rules (1)–(3) with the active agent as initiator
--   - reading: 'signals an Anomaly otherwise' → the complement of the no-anomaly event of p.21 within the round; reason: the anomaly check of p.21 tests exactly this condition
--   - generalization: w = Θ(log n) with the free-agent bound of the population n_w → every C > 1, every w with 3 ≤ w ≤ a log₂ n, any a > 0; at least 2^{w−1} + (1 − 1/C)n free agents; reason: the proof uses only w = O(log n) and (1 − 1/C)n free agents throughout; the simulation is an instance
--   - encoding: w ≥ 3 → 3 ≤ w; reason: for w ≤ 2 the delegation state p*(w − 2) has no rule: the source's w is large
--   - encoding: one round → c·n·log₂ n interactions; reason: a round lasts Θ(log n) time
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Lemma 3 and rules (1)–(3), p.21 (PDF p.22), proof pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_PopRAM_Protocol
import Definitions.Def_PopRAM_WeightCreation

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Lemma 3** with rules (1)–(3) (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version
sha256 f13223b3…, p.21, PDF p.22). "The protocol WeightCreation(w) correctly creates weights
P₀, P₁, …, P_{w−2} whp in one round and signals an Anomaly otherwise. It uses Θ(w²) states."

1. For every `C > 1`, `a > 0`, `η > 0` there are `c` and `n₀` such that for every `n ≥ n₀`, every
   `w` with `3 ≤ w ≤ a log₂ n`, and every configuration with exactly one agent, the leader, in
   `lead0`, every other agent free or inert, and at least `2^{w−1} + (1 − 1/C)n` free agents:
   - with probability at least `1 − n^{-η}`, within `c·n log₂ n` interactions (one round,
     `Θ(log n)` time) the configuration satisfies `wcDone` (no anomaly condition);
   - on every schedule, at every time at which `wcDone` holds, for every `k ≤ w − 2` exactly `2^k`
     agents are in `p_k(0)` (the weight `P_k`), and the configuration is silent.
2. The weight states number `Θ(w²)`: there are `c₁, c₂ > 0` with `c₁w² ≤ |weightStates w| ≤ c₂w²` for
   all `w ≥ 3`.

**Formalization Note** The anomaly of p.21 is signalled "if … the leader failed to delegate the
creation of weights or some follower remains in state p_k(i) or p∗(i), for i > 0"; `wcDone` is its
complement, so "signals an Anomaly otherwise" is the first bullet's complement event. One round is
`c log n` time. -/
theorem lemma_3 :
    (∀ C : ℝ, 1 < C → ∀ a η : ℝ, 0 < a → 0 < η → ∃ c : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ w : ℕ, 3 ≤ w →
      (w : ℝ) ≤ a * Real.logb 2 n →
      ∀ (c₀ : Fin n → WCState) (a₀ : Fin n), c₀ a₀ = .lead0 →
        (∀ b, b ≠ a₀ → c₀ b = .free ∨ c₀ b = .X) →
        (2 : ℝ) ^ (w - 1) + (1 - 1 / C) * n ≤ countIn c₀ (· = WCState.free) →
        sched n {ω | ¬ ∃ t : ℕ, (t : ℝ) ≤ c * n * Real.logb 2 n ∧ run (wcδ w) c₀ ω t ∈ wcDone}
            ≤ whpBound n η ∧
        ∀ ω t, run (wcδ w) c₀ ω t ∈ wcDone →
          (∀ k ≤ w - 2, countIn (run (wcδ w) c₀ ω t) (· = WCState.p k 0) = 2 ^ k) ∧
          Silent (wcδ w) (run (wcδ w) c₀ ω t)) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ w : ℕ, 3 ≤ w →
      c₁ * w ^ 2 ≤ (weightStates w).card ∧ ((weightStates w).card : ℝ) ≤ c₂ * w ^ 2 := by sorry

end PopRAM
