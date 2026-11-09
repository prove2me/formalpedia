-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_2_3
-- name    : RecoveryStorage3SUM.Adaptive.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:16.755323+00:00
-- url     : https://prove2.me/theorems/de7a4c34-f305-4ca7-9b71-0fb96941c0f5
-- title:
--   Lemma 2.3 (Fiat–Naor) — inverting a self-map with $\widetilde O(\sqrt{N^3q(f)/T})$ stored bits
-- statement:
--   Let $f:[N]\to[N]$ be a self-map accessed through unit-cost evaluations, let $1\le T\le N$, and let $d>0$. There are programs and constants, independent of $f,N,T$, such that with
--   $$S=C\log^e(N+2)\sqrt{N^3q(f)/T}$$
--   the following hold, where $q(f)$ is the collision probability.
--
--   1. On every coin sequence the construction, started on $N,T$, halts within $C\log^e(N+2)(N+S)$ steps and stores at most $S$ bits.
--   2. Except with probability $(N+2)^{-d}$ over the coins of the construction, the query program, with no coins of its own, answers every $y\in[N]$ simultaneously within $C\log^e(N+2)\,T$ steps. It returns some $x\in f^{-1}(y)$, or $\bot$ if $f^{-1}(y)=\emptyset$.
--
--   This inverter replaces the stored lists of pairs in the data structure of Theorem 1.1.
--
--   Differences from the source:
--   - reading: "w.h.p over the construction randomness" → for every $d>0$, failure at most $(N+2)^{-d}$; the query has no coins; reason: the only randomness the lemma names is the constructions; polynomial tails are the sources convention
--   - reading: "a data structure of size $S$ in $\widetilde O(N+S)$ time" → size and time hold on every coin sequence; reason: the lemma attaches no probability to them; this is the stronger of the two readings
--   - encoding: constant-time oracle for $f$ (p.4) → unit-cost instruction $[i]:=f([j])$; reason: the same access model
--   - encoding: $\widetilde O$; size in words → $C\log^e(N+2)$ factors; size in bits; reason: bits and $O(\log N)$-bit words differ by a logarithmic factor
--   - encoding: $T\le N$ → $1\le T\le N$; reason: $\widetilde O(0)$ time is meaningless; the source calls $T$ a time bound
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 2.3, p.6

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_OracleMachine

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MatroidSensOracle in
/-- Lemma 2.3 (Fiat–Naor), p.6. For every self-map `f` of `[N]`, accessed only through unit-cost
evaluations, and every `1 ≤ T ≤ N`: the construction, started on `[N, T]`, always halts within
`Õ(N + S)` steps with a stored string of at most `S = Õ(√(N³ q(f) / T))` bits, and except with probability
`(N + 2)^{-d}` over its coins the deterministic query answers **every** `y ∈ [N]` within `Õ(T)` steps,
with some `x ∈ f⁻¹(y)`, or `⊥` if `f⁻¹(y)` is empty. -/
theorem lemma_2_3 (d : ℝ) (hd : 0 < d) :
    ∃ (b e : ℕ) (C : ℝ) (P Q : List OInstr), 0 < b ∧ 0 < C ∧ OCoinFree Q ∧
      ∀ (N T : ℕ) (f : ℕ → ℕ), 1 ≤ N → 1 ≤ T → T ≤ N → IsSelfMap N f →
        let w := wordWidth b N
        let S : ℝ := C * Real.log ((N : ℝ) + 2) ^ e *
          Real.sqrt ((N : ℝ) ^ 3 * collisionProb N f / (T : ℝ))
        let TP : ℕ := ⌈C * Real.log ((N : ℝ) + 2) ^ e * ((N : ℝ) + S)⌉₊
        let TQ : ℕ := ⌈C * Real.log ((N : ℝ) + 2) ^ e * (T : ℝ)⌉₊
        (∀ ω : Coins, ∃ mP, oexec N f P ω TP 0 0 (loadWords w [(N : ℤ), (T : ℤ)]) = some mP ∧
          (storedLength mP : ℝ) ≤ S) ∧
        coinLaw {ω : Coins | ¬ ∃ mP, oexec N f P ω TP 0 0 (loadWords w [(N : ℤ), (T : ℤ)]) = some mP ∧
            ∀ y < N, ∀ ω' : Coins, ∃ m,
              oexec N f Q ω' TQ 0 0 (queryMemory w mP [(y : ℤ)]) = some m ∧
                InvertsAt N f y (decodeAnswer m)} ≤
          ENNReal.ofReal (((N : ℝ) + 2) ^ (-d)) := by sorry

end RecoveryStorage3SUM.Adaptive
