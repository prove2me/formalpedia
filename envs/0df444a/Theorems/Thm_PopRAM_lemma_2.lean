-- Prove2me | Theorems.Thm_PopRAM_lemma_2
-- name    : PopRAM.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:23:57.827284+00:00
-- url     : https://prove2.me/theorems/77bd1e13-a503-4542-bfb3-efa3cba3ef74
-- title:
--   Lemma 2 — RegInit allocates $M=\rho'w$ register bits stably and silently in $O(M)$ time, in expectation and whp
-- statement:
--   For every $C>1$, $a>0$ and $\eta>0$ there is a constant $K$ such that the following holds for every $n\ge2$. Let $M\ge\max(1,a\log_2 n)$ be the number of register bits to allocate, and start from a configuration in which exactly one agent, the leader, is in $L_0$, every other agent is free or inert, and at least $M+(1-1/C)n$ agents are free. Let $T$ be the first time the leader is in $L_M$. Then
--
--   1. $\mathbb E[T]\le K\,n\,M$ interactions (time $O(M)$);
--   2. $\Pr[T> K\,n\,M]\le n^{-\eta}$;
--   3. on every schedule with $T<\infty$, each bit $m<M$ is held by exactly one agent at time $T$, and the configuration at time $T$ is silent.
--
--   In the simulation $M=\rho'w$ with $w=\Theta(\log n)$, so register initialisation takes $O(\rho'w)$ time; both the MC+ simulation and the backup use it.
--
--   **Formalization Note** The free-agent bound of Fact 1 (at least $(1-1/C)n$ free agents throughout) is guaranteed by $M+(1-1/C)n$ initially free agents.
--
--   Differences from the source:
--   - reading: 'Assuming a unique leader and the free-agent bound of Fact 1' → one agent in L_0, the others free or inert, at least M + (1 − 1/C)n free agents initially; reason: allocation consumes M free agents, so (1 − 1/C)n remain free throughout
--   - generalization: M = ρ′w register bits with w = Θ(log n) → every M with M ≥ max(1, a log₂ n), every a > 0; reason: the proof uses only M ≥ w = Θ(log n); M = ρ′w is an instance
--   - reading: L + φ → L + (R; r, i, 0) → the rule in both orientations; reason: the proof counts probability 2p/n per interaction
--   - encoding: O(ρ′w) time in expectation and whp; 'stably' → E[T] ≤ K·n·M and P(T > K·n·M) ≤ n^{−η} in interactions; finiteness follows from the expectation; reason: time = interactions / n
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Lemma 2, p.7 (PDF p.8), proof p.8 (PDF p.9); Protocol 3, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_PopRAM_Protocol
import Definitions.Def_PopRAM_RegInit

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Lemma 2** (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version sha256 f13223b3…,
p.7, PDF p.8; Protocol 3, p.14, PDF p.15). "Assuming a unique leader and the free-agent bound of
Fact 1, Protocol 3 stably and silently initialises ρ′ registers of w bits each, in O(ρ′w) time both
in expectation and whp."

For every `C > 1`, `a > 0` and `η > 0` there is `K` such that: for every `n ≥ 2`, every number
`M ≥ max(1, a log₂ n)` of register bits (`M = ρ′w`) and every configuration with exactly one agent,
the leader, in `L 0`, every other agent free or inert, and at least `M + (1 − 1/C)n` free agents,
the allocation time `T` (first time the leader holds `L M`) satisfies
1. `E[T] ≤ K·n·M` interactions (time `O(M)`);
2. `P(T > K·n·M) ≤ n^{-η}`;
3. on every schedule with `T < ∞`: every bit `m < M` is held by exactly one agent at time `T`, and
   the configuration at time `T` is silent.

**Formalization Note** "The free-agent bound of Fact 1" (at least `(1 − 1/C)n` free agents
throughout) is ensured by `M + (1 − 1/C)n` initially free agents, since allocation uses `M` of them.
`M ≥ a log₂ n` reflects the proof's use of `M ≥ w = Θ(log n)` for the Chernoff bound. -/
theorem lemma_2 (C : ℝ) (hC : 1 < C) (a η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → ∀ M : ℕ, 1 ≤ M → a * Real.logb 2 n ≤ M →
      ∀ (c₀ : Fin n → RIState) (a₀ : Fin n), c₀ a₀ = .L 0 →
        (∀ b, b ≠ a₀ → c₀ b = .free ∨ c₀ b = .X) →
        (M : ℝ) + (1 - 1 / C) * n ≤ countIn c₀ (· = RIState.free) →
        ∫⁻ ω, (hit (regInitδ M) c₀ (regInitDone M) ω : ℝ≥0∞) ∂(sched n)
            ≤ ((K * n * M : ℕ) : ℝ≥0∞) ∧
        sched n {ω | ((K * n * M : ℕ) : ℕ∞) < hit (regInitδ M) c₀ (regInitDone M) ω}
            ≤ whpBound n η ∧
        ∀ ω, hit (regInitδ M) c₀ (regInitDone M) ω ≠ ⊤ →
          (∀ m < M, ∃! b, run (regInitδ M) c₀ ω (hit (regInitδ M) c₀ (regInitDone M) ω).toNat b
              = .R m) ∧
          Silent (regInitδ M)
            (run (regInitδ M) c₀ ω (hit (regInitδ M) c₀ (regInitDone M) ω).toNat) := by sorry

end PopRAM
