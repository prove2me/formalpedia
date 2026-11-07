-- Prove2me | Theorems.Thm_PopRAM_fact_3
-- name    : PopRAM.fact_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:24:14.380866+00:00
-- url     : https://prove2.me/theorems/896db743-676b-471e-a7d6-ba1adb0f25d7
-- title:
--   Fact 3 — every RAM instruction (with INC, DEC) is emulated correctly by at most $3w$ calls of GET and PUT (corrected: $a_{\max}\ge1$)
-- statement:
--   Let $w\ge1$ and $1\le a_{\max}\le 2^{w-1}$. For every RAM instruction $I$ of Table 3 (LOAD, ADD, SUB, both indirect COPYs, JGE, INC, DEC), every register file $F$ and every instruction pointer, the reduction of $I$ to GET and PUT (Protocols 1, 2, 4–9):
--
--   1. reports InvalidAddress exactly when $I$ uses an indirect address whose signed value is outside $\{0,\dots,a_{\max}-1\}$, and otherwise returns the same next instruction pointer as the word-level step;
--   2. when the word-level step is valid, ends with exactly its register file (arithmetic modulo $2^w$, JGE on the signed value);
--   3. executes at most $3w$ atomic subroutines GET and PUT.
--
--   Moreover $\mathrm{SET}(r,r_p)$ returns $[r_p]$ when its signed value lies in $\{0,\dots,a_{\max}-1\}$ and InvalidAddress otherwise, in particular for every negative word.
--
--   Clause 3 is Fact 3; clauses 1–2 are the "Result" lines of the protocols. The reductions are shared by the MC+ simulation and the backup, so instruction emulation costs at most $3w$ bit accesses in both.
--
--   Differences from the source:
--   - generalization: Fact 3: at most 3w calls of GET and PUT → also: the reduction computes exactly the word-level step and SET detects exactly the invalid addresses; reason: the 'Result:' lines of Protocols 1–9 and Table 3 assert these; the count is clause 3
--   - correction: SET 'rejects an index outside {0, …, a_max − 1}' → 1 ≤ a_max assumed; reason: for a_max = 0 and the word 0, Protocol 1 never tests a bit and returns r = 0, which is outside the empty range
--   - reading: 'For sufficiently large w, all ρ′ … register addresses fit in non-negative w-bit words' (p.6) → a_max ≤ 2^{w−1}; reason: without it a negative word with a large unsigned value would pass SET's test
--   - encoding: registers as words of w bits accessed bit by bit → register file ℕ → BitVec w in a state monad counting GET/PUT calls; reason: Lean representation
--   - encoding: word length w (a word has a sign bit, which JGE reads) → w ≥ 1; reason: at w = 0 there are no words to emulate, while the JGE reduction would still make one call against 3w = 0
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Fact 3, p.9 (PDF p.10), with Table 3 and Protocols 1–2, pp.8–9 (PDF pp.9–10), and Protocols 4–9, pp.15–17 (PDF pp.16–18)

import Mathlib
import Definitions.Def_PopRAM_Reductions

set_option autoImplicit false

namespace PopRAM

/-- **Fact 3** with Table 3 and Protocols 1, 2, 4–9 (Gąsieniec, Grodzicki, Stachowiak,
arXiv:2611.06178, held version sha256 f13223b3…, p.9, PDF p.10; pp.15–17, PDF pp.16–18). "Emulation
of each RAM instruction (including INC and DEC) requires the execution of at most 3w atomic
subroutines GET() and PUT()."

Let `w ≥ 1` and `1 ≤ a_max ≤ 2^{w−1}`. For every RAM instruction `I` (Table 3, including INC and DEC), every
register file `F` and instruction pointer `ip`, running the reduction of `I` from `F`:
1. it reports `InvalidAddress` exactly when the instruction's indirect address is invalid, and
   otherwise returns the instruction pointer of the word-level step;
2. when the word-level step is valid, the reduction ends in exactly its register file;
3. it makes at most `3w` calls of `GET` and `PUT`.

Moreover `SET(r, rp)` (Protocol 1) returns `[rp]` when the signed value of `[rp]` lies in
`{0, …, a_max − 1}`, and `InvalidAddress` otherwise (including every negative word).

**Formalization Note** Clauses 1–2 and the SET clause are the "Result:" lines of Protocols 1–9 and
the reductions of Table 3; Fact 3 itself is clause 3. `w ≥ 1`: a word has a sign bit, which JGE
reads; at `w = 0` the JGE reduction makes one call and `3w = 0`. -/
theorem fact_3 (w amax : ℕ) (hw : 1 ≤ w) (hamax1 : 1 ≤ amax) (hamax : amax ≤ 2 ^ (w - 1)) :
    (∀ (I : RamInstr) (F : ℕ → BitVec w) (ip : ℕ),
      ((reduce amax ip I).run ⟨F, 0⟩).1 = (ramSpec amax ip F I).map Prod.snd ∧
      (∀ F' ip', ramSpec amax ip F I = some (F', ip') → ((reduce amax ip I).run ⟨F, 0⟩).2.regs = F') ∧
      ((reduce amax ip I).run ⟨F, 0⟩).2.calls ≤ 3 * w) ∧
    ∀ (F : ℕ → BitVec w) (rp : ℕ), ((SET amax rp).run ⟨F, 0⟩).1 = validAddr amax (F rp) := by sorry

end PopRAM
