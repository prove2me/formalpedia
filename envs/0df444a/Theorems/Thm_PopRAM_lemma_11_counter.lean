-- Prove2me | Theorems.Thm_PopRAM_lemma_11_counter
-- name    : PopRAM.lemma_11_counter
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:52.462014+00:00
-- url     : https://prove2.me/theorems/1901433e-f623-490f-8f99-1c5cc48549b6
-- title:
--   Proof of Lemma 11 — the output counter runs $v$ assignments and $v+1\le2^{w-1}$ DEC/JGE pairs down to $-1$ without overflow
-- statement:
--   Let $w\ge1$ and $0\le v<2^{w-1}$. The counter loop of Protocol 20 (repeat: $\mathrm{DEC}(r_c)$; if $[r_c]\ge0$ assign one output agent, else stop), started from the $w$-bit word of $v$:
--
--   1. performs exactly $v$ assignments and $v+1$ DEC/JGE pairs, with $v+1\le 2^{w-1}$, and ends with the all-ones word, whose two's-complement value is $-1$;
--   2. after the $j$-th DEC, for every $j\le v+1$, the counter's signed value is $v-j$, so no overflow occurs.
--
--   This is the arithmetic behind the backup's binary-to-unary output conversion: exactly $[r^{out}_i]$ output agents are created.
--
--   **Formalization Note** The loop is run with a fuel of $2^w$ iterations; clause 1 shows it stops by itself before the fuel is exhausted.
--
--   Differences from the source:
--   - encoding: the loop DEC(r_c), JGE(r_c, ASSIGN:) → a recursive loop with a fuel of 2^w iterations; reason: termination is part of the conclusion: the fuel is not exhausted
--   - encoding: a signed counter of word length w → w ≥ 1; reason: at w = 0 there is no sign bit and no value −1
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), proof of Lemma 11, p.35 (PDF p.36), with Protocol 20, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_PopRAM_Countdown

set_option autoImplicit false

namespace PopRAM

/-- **The counter loop in the proof of Lemma 11** (Gąsieniec, Grodzicki, Stachowiak,
arXiv:2611.06178, held version sha256 f13223b3…, p.35, PDF p.36, with Protocol 20). "To convert the
i-th output value, the leader emulates one instruction COPY, followed by at most 2^{w−1} pairs of DEC
and JGE instructions and exactly [r^out_i] assignments of an output state to a free agent. Since
0 ≤ [r^out_i] < 2^{w−1}, the signed counter runs down to −1 without overflow."

For `w ≥ 1` and `0 ≤ v < 2^{w−1}`, the counter loop of Protocol 20 started from the `w`-bit word of
`v` (with a fuel of `2^w` iterations, which it does not exhaust):
1. performs exactly `v` assignments and `v + 1` DEC/JGE pairs, with `v + 1 ≤ 2^{w−1}`, and ends with
   the all-ones word, whose signed value is `−1`;
2. after the `j`-th DEC, for every `j ≤ v + 1`, the counter's signed value is `v − j` (no
   overflow). -/
theorem lemma_11_counter (w v : ℕ) (hw : 1 ≤ w) (hv : v < 2 ^ (w - 1)) :
    countdown (2 ^ w) (BitVec.ofNat w v) 0 0 = (v, v + 1, BitVec.allOnes w) ∧
    (BitVec.allOnes w).toInt = -1 ∧ v + 1 ≤ 2 ^ (w - 1) ∧
    ∀ j ≤ v + 1, ((fun x : BitVec w => x - 1)^[j] (BitVec.ofNat w v)).toInt = (v : ℤ) - j := by sorry

end PopRAM
