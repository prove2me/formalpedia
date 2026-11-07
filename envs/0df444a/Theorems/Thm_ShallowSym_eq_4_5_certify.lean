-- Prove2me | Theorems.Thm_ShallowSym_eq_4_5_certify
-- name    : ShallowSym.eq_4_5_certify
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:47.259756+00:00
-- url     : https://prove2.me/theorems/69331f21-dd48-4348-ab88-0f11cc1bbb71
-- title:
--   Eqs. (4)–(5): a test is an AND of pair functions, and a passing test certifies $|x|\equiv t \pmod k$
-- statement:
--   Let $k\ge 1$, let $\beta$ be a partition of the $n$ coordinates into $k$ blocks with block weights $w_1,\dots,w_k$, let $s_1,\dots,s_k\in\mathbb Z/k\mathbb Z$ be shifts, $t\in\mathbb N$ and $x\in\{0,1\}^n$.
--
--   1. (Eq. (5).) The test passes at $x$ — the values $w_1+s_1,\dots,w_k+s_k$ are distinct modulo $k$ — if and only if
--   $$\bigwedge_{1\le i<j\le k} 1\big[w_i+s_i\not\equiv w_j+s_j \pmod k\big](x) = 1.$$
--   2. (Eq. (4).) If the shifts satisfy $\sum_{i=1}^k s_i\equiv\binom k2-t\pmod k$ and the test passes at $x$, then
--   $$|x|\equiv t\pmod k.$$
--
--   These tests are the building blocks of the construction: each certifies the weight modulo $k$ without prescribing the individual block weights.
--
--   Differences from the source:
--   - generalization: k blocks of length at most ⌈n/k⌉ → an arbitrary map β : Fin n → Fin k (any block sizes); reason: the length bound plays no role in this step; specializes to the paper's partitions
--   - encoding: blocks 1, …, k and shifts in {0, 1, …, k − 1} → blocks Fin k (0-based) and shifts in ZMod k; reason: Lean convention; same instances
--   - encoding: k blocks (k a number of blocks, implicitly k ≥ 1) → instance [NeZero k]; reason: excludes only k = 0, where there are no blocks and ZMod 0 = ℤ is not arithmetic modulo k; same instances
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §4 'Anatomy of a test', eqs. (4)–(5), p.11; depth-3 version §3, eqs. (2)–(3), p.8

import Mathlib
import Definitions.Def_ShallowSym_pairFn
import Definitions.Def_ShallowSym_ShiftConstraint
import Definitions.Def_ShallowSym_TestPasses

namespace ShallowSym

/-- §4 "Anatomy of a test", eqs. (4)–(5), p.11 (the depth-3 version is §3, eqs. (2)–(3), p.8).
V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"each test splits the input x into k blocks of length at most ⌈n/k⌉, and fixes shifts
s1, . . . , sk ∈ {0, 1, . . . , k − 1} satisfying ∑_{i=1}^{k} si ≡ (k choose 2) − t (mod k). (4)
Let wi be the weight of block i. The test passes if w1 + s1, . . . , wk + sk are all distinct
modulo k, which implies that the weight of x is t mod k. In other words, the test computes the
function ⋀_{1≤i<j≤k} 1[wi + si ≢ wj + sj (mod k)]. (5)"

For `k ≥ 1`, a partition `β : Fin n → Fin k`, shifts `s` and `x ∈ {0,1}^n`:
1. the test passes at `x` iff every pair function `1[w_i + s_i ≢ w_j + s_j (mod k)]`,
   `i < j`, is true at `x` (eq. (5));
2. if the shifts satisfy (4) for `t` and the test passes at `x`, then `|x| ≡ t (mod k)`.

**Formalization Note.** Blocks are `Fin k` (0-based), shifts are in `ZMod k`; the block length
bound ⌈n/k⌉ plays no role here, so `β` is arbitrary. -/
theorem eq_4_5_certify {n k : ℕ} [NeZero k] (β : Fin n → Fin k) (s : Fin k → ZMod k)
    (t : ℕ) (x : Cube n) :
    (TestPasses β s x ↔ ∀ i j : Fin k, i < j → pairFn β s i j x = true) ∧
    (ShiftConstraint k t s → TestPasses β s x →
      ((weight x : ℕ) : ZMod k) = ((t : ℕ) : ZMod k)) := by sorry

end ShallowSym
