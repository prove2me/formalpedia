-- Prove2me | Theorems.Thm_ProperHalfspace_theorem_1
-- name    : ProperHalfspace.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:07.21345+00:00
-- url     : https://prove2.me/theorems/c82ede0a-6d03-4bec-9767-10b60faf5484
-- title:
--   Theorem 1 — a query-based proper agnostic learner for halfspaces (corrected: $n\ge1$)
-- statement:
--   There is one finite program on the membership-query real RAM and a universal constant $C$ such that the following holds for every $n\ge1$, every $\varepsilon\in(0,1/2)$ and every $f:\{\pm1\}^n\to\{\pm1\}$, the program reading $f$ only through queries.
--
--   1. On every coin tape the program halts after at most $Cn\varepsilon^{-28}$ queries and at most
--   $$Cn^3\varepsilon^{-30}+2^{C\varepsilon^{-14}\log(1/\varepsilon)}$$
--   units of work.
--   2. With probability at least $2/3$, the halfspace $g(x)=\operatorname{sign}(w\cdot x-\theta)$ it outputs satisfies
--   $$\mathrm{err}_f(g)\le\mathrm{OPT}_f+\varepsilon.$$
--
--   According to the paper (p.2), this is the first agnostic learner for halfspaces on the Boolean cube with running time polynomial in $n$ and an exponent independent of $\varepsilon$. Its output is itself a halfspace.
--
--   **Formalization Note** The input is $n$ in pointer $0$ and $\varepsilon$ in memory cell $0$; the output is $w_i$ in cell $i$, for $i<n$, and $\theta$ in cell $n$.
--
--   Differences from the source:
--   - correction: every n, with O(nε⁻²⁸) queries → n ≥ 1; reason: false at n = 0: both constants f = ±1 satisfy every assumption with OPT = 0, the query bound is 0, and error ≤ ε < 1/2 forces the right constant, which no query-free algorithm outputs with probability ≥ 2/3 for both
--   - reading: the real-RAM model, with no instruction set named (p.2) → the local machine ProperHalfspace.Machine, with exact + − × ÷, rational literals, fair coins, query at cost n, and no √, floor, eigensolver or uniform real draw; reason: the page names no instructions; every primitive added would weaken the theorem
--   - reading: "there is an algorithm (Algorithm 1)" → ∃ P, a program of the machine; reason: Algorithm 1 as written uses an exact eigendecomposition, which is not a program of this machine
--   - reading: "runs in time at most" and "makes at most" → both bounds hold on every coin tape; reason: the proof says "These bounds hold even when the matrix estimate fails" (p.29)
--   - encoding: O(·) → one constant C chosen before all the data; reason: the page's constants are universal (p.10)
--   - encoding: probability over the algorithm's coins → a count over coin tapes of length the work bound, rounded up; reason: a run within B units of work reads at most B coins
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Theorem 1, p.2 (restated p.21); Algorithm 1, p.27

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace
import Definitions.Def_ProperHalfspace_Machine

namespace ProperHalfspace

/-- Theorem 1, p.2 (query-based proper agnostic learner). De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). One finite
program on the membership-query real RAM, with one universal `C`: for every `n ≥ 1`, `ε ∈ (0, 1/2)` and `f : {±1}ⁿ → {±1}`, on every coin
tape the program halts after at most `C n ε⁻²⁸` queries and `C n³ ε⁻³⁰ + 2^{C ε⁻¹⁴ log(1/ε)}` work, and with probability at least `2/3` its
output `(w, θ)` satisfies `err_f(sign(w · x − θ)) ≤ OPT_f + ε`.

**Formalization Note.** The input is `n` in pointer `0` and `ε` in `M[0]`; the output is `M[i] = wᵢ` for `i < n` and `M[n] = θ`, so every halted
state decodes to a halfspace. The program may read `f` only through `query`. The probability is the count over tapes of length the work
bound (rounded up), which no run reads past. The bounds hold on every tape, as the proof says on p.29. -/
theorem theorem_1 : ∃ P : Program, Admissible P ∧ ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ f : Cube n → ℝ, IsBoolean f →
      let W : ℝ := (C : ℝ) * (n : ℝ) ^ 3 * (1 / ε) ^ 30 +
        (2 : ℝ) ^ ((C : ℝ) * (1 / ε) ^ 14 * Real.log (1 / ε))
      (∀ tape : ℕ → Bool, ∃ t : ℕ,
        let s := run P f tape (goalInit n ε) t
        s.halted = true ∧ (s.queries : ℝ) ≤ (C : ℝ) * (n : ℝ) * (1 / ε) ^ 28 ∧ (s.work : ℝ) ≤ W) ∧
      2 / 3 ≤ tapeProb ⌈W⌉₊ (fun tape => ∃ t : ℕ,
        let s := run P f tape (goalInit n ε) t
        s.halted = true ∧ err f (ltf (decodeNormal n s) (decodeThreshold n s)) ≤ opt f + ε) := by sorry

end ProperHalfspace
