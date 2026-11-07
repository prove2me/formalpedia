-- Prove2me | Theorems.Thm_ShallowSym_shift_count
-- name    : ShallowSym.shift_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:01:25.555202+00:00
-- url     : https://prove2.me/theorems/a18ebebf-31b4-464f-9587-511c7a3b4809
-- title:
--   $k^{k-1}$ admissible shift vectors, of which exactly $k!$ certify a valid input
-- statement:
--   Let $k\ge 1$, $t\in\mathbb N$, let $\beta$ partition the $n$ coordinates into $k$ blocks, and let $x\in\{0,1\}^n$ be **valid**: $|x|\equiv t\pmod k$. Among the shift vectors $s\in(\mathbb Z/k\mathbb Z)^k$:
--
--   1. exactly $k^{k-1}$ satisfy the constraint $\sum_i s_i\equiv\binom k2-t\pmod k$;
--   2. exactly $k!$ of these make the test pass at $x$.
--
--   So a uniformly random admissible test passes at a fixed valid input with probability $k!/k^{k-1}$.
--
--   Differences from the source:
--   - generalization: k blocks of length at most ⌈n/k⌉ → an arbitrary partition β : Fin n → Fin k; reason: the count does not use the block lengths; specializes to the paper's partitions
--   - encoding: shifts in {0, 1, …, k − 1}, blocks 1, …, k → s : Fin k → ZMod k; reason: Lean convention; same instances
--   - encoding: k blocks (k a number of blocks, implicitly k ≥ 1) → instance [NeZero k]; reason: excludes only k = 0, where there are no blocks and ZMod 0 = ℤ is not arithmetic modulo k; same instances
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §3 'Coverage with random tests', p.9; used for depth d in §4, p.11

import Mathlib
import Definitions.Def_ShallowSym_ShiftConstraint
import Definitions.Def_ShallowSym_TestPasses

namespace ShallowSym

open scoped Classical in
/-- §3 "Coverage with random tests", p.9 (used for depth d on p.11: "By the same argument as in
the depth-3 case"). V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"There are k^{k−1} total choices of shifts, since the first k − 1 can be chosen arbitrarily, and
the last is fixed by their sum. Of these, k! certify any fixed valid x."

For `k ≥ 1`, a target `t`, a partition `β : Fin n → Fin k` and a valid input `x`
(`|x| ≡ t (mod k)`): exactly `k^{k−1}` shift vectors `s ∈ (ℤ/k)^k` satisfy constraint (2)/(4),
and exactly `k!` of them make the test pass at `x`. -/
theorem shift_count {n k : ℕ} [NeZero k] (t : ℕ) (β : Fin n → Fin k) (x : Cube n)
    (hx : ((weight x : ℕ) : ZMod k) = ((t : ℕ) : ZMod k)) :
    (Finset.univ.filter (fun s : Fin k → ZMod k => ShiftConstraint k t s)).card = k ^ (k - 1) ∧
    (Finset.univ.filter (fun s : Fin k → ZMod k =>
      ShiftConstraint k t s ∧ TestPasses β s x)).card = k.factorial := by sorry

end ShallowSym
