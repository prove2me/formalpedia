-- Prove2me | Theorems.Thm_PairwiseRealize_theorem_C_1
-- name    : PairwiseRealize.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:37.644924+00:00
-- url     : https://prove2.me/theorems/60de0b4d-714e-4ae6-a4d5-9e0209dce124
-- title:
--   Theorem C.1, p.15 — deterministic rounding with $\|A(q-p)\|_\infty\le40000\lceil\sqrt m\rceil$ in polynomial bit cost
-- statement:
--   There are a deterministic machine and constants $C,d$ such that for all $s\le m$, every $A\in\{0,1\}^{m\times s}$ and every rational $p\in[0,1]^s$, on input $(m,s,A,p)$ the machine halts within $C(m+|\mathrm{enc}(p)|+1)^d$ steps with some $q\in\{0,1\}^s$ on its tape, and
--
--   $$\|A(q-p)\|_\infty\le40000\lceil\sqrt m\rceil.$$
--
--   The mission uses this to round basic solutions, both of the outer linear program and at each node.
--
--   Differences from the source:
--   - reading: "a deterministic algorithm", "bit cost" → a RandomMachine whose transition ignores the random bit; its number of steps; reason: a Post–Turing machine counts bit operations up to a polynomial, and the matrix takes ms ≤ m² symbols, so the bound is polynomial in m and the encoding length of p
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), Theorem C.1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_ContingencyTables
import Definitions.Def_PairwiseRealize_Machine

namespace PairwiseRealize

open OAI.MatchingFPRAS

/-- **Theorem C.1, p.15 (PDF p.16).** K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean
Statistics*, STOC 2027 submission (manuscript sha256 62090516…): "Theorem C.1. For A ∈ {0, 1}^{m×s},
s ≤ m, and rational p ∈ [0, 1]^s, a deterministic algorithm returns q ∈ {0, 1}^s with
‖A(q − p)‖∞ ≤ 40000⌈√m⌉. Its bit cost is polynomial in m and the encoding length of p."

There are a deterministic machine `M` and constants `C, d` such that, for all `s ≤ m`, every
`A ∈ {0,1}^{m×s}` and every rational `p ∈ [0,1]^s`, on input `(m, s, A, p)` the machine has halted
within `C(m + |enc p| + 1)^d` steps with some `q ∈ {0,1}^s` on its tape, and
`|Σⱼ A_{rj}(qⱼ − pⱼ)| ≤ 40000⌈√m⌉` for every row `r`.

**Formalization Note** "A deterministic algorithm" is a `RandomMachine` (the published randomized
Post–Turing machine of `ContingencyTables`) whose transition ignores the random bit; its bit cost is
its number of steps. `|enc p|` is the length of the encoding of `p` (reduced numerators and
denominators in binary); the matrix takes `ms ≤ m²` symbols, so the bound is polynomial in the whole
input length. The conclusion is required on every bit string of that length, which for a
deterministic machine is the single run. -/
theorem theorem_C_1 :
    ∃ (M : RandomMachine) (C d : ℕ), Deterministic M ∧
      ∀ (m s : ℕ), s ≤ m → ∀ (A : Fin m → Fin s → Bool) (p : Fin s → ℚ),
        (∀ j, 0 ≤ p j ∧ p j ≤ 1) →
        ∀ bits : Fin (C * (m + (ratVecCode p).length + 1) ^ d) → Bool,
          ∃ q : Fin s → Bool, OutputsBits M (c1Input m s A p) bits q ∧
            ∀ r : Fin m, |∑ j, ((if A r j then 1 else 0 : ℝ) * ((if q j then 1 else 0 : ℝ) - p j))| ≤
              40000 * (⌈Real.sqrt m⌉₊ : ℝ) := by sorry

end PairwiseRealize
