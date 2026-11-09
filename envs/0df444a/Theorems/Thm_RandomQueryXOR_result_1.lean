-- Prove2me | Theorems.Thm_RandomQueryXOR_result_1
-- name    : RandomQueryXOR.result_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:12:22.318052+00:00
-- url     : https://prove2.me/theorems/98be9014-48ed-4015-8519-40a470c7d4dc
-- title:
--   Result 1 — an XOR-function of sensitivity $k$ needs $T(S+\log T)=\Omega(n\cdot k)$ in the random query model
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $f:\{0,1\}^n\to\{0,1\}$ be any function and $g=f\circ\oplus_2:\{0,1\}^{2n}\to\{0,1\}$,
--   $$
--   g(y)=f\bigl(y(1)\oplus y(2),\dots,y(2n-1)\oplus y(2n)\bigr),
--   $$
--   with sensitivity $k=\mathrm{sens}[g]$. If a randomized branching program of width $2^S$ and length $T$, reading samples $(i,y(i))$ with $i$ drawn i.i.d. uniformly from $[2n]$, computes $g$ with probability of success at least $2/3$ on every input, then
--   $$
--   T\cdot(S+\log_2T)\ \ge\ c\cdot n\cdot k .
--   $$
--
--   The bound depends on sensitivity rather than total influence, so it applies to low-influence functions: for equality and for Tribes-type functions it is a nearly quadratic time-space lower bound, which is tight up to logarithmic factors.
--
--   Differences from the source:
--   - reading: T · (S + log T) = Ω(·) → ∃ c > 0, chosen before n, f, S, T and the program, with c · (·) ≤ T · (S + log₂ T) for all of them; reason: the uniform reading of Ω; for the finitely many small n not covered by the proof's 'sufficiently large n', a correct program for non-constant g has T ≥ 1 and S ≥ 1, so a smaller c covers them
--   - encoding: a randomized branching program: a distribution D^A_n on programs with per-node distributions over outgoing edges → a probability distribution (WildeQIT.FinDist) on deterministic layered programs DetBP (2^S) _ T; reason: a run visits one node per layer, so independent per-node edge choices fold into a distribution on deterministic programs; the paper does the same in π_two step (ii)
--   - encoding: probability of success at least 2/3, the minimum over inputs → 2/3 ≤ success probability on every input y; reason: a lower bound on a minimum is a lower bound at every input
--   - encoding: [2n] with pairs (2i − 1, 2i) → Fin (2 * n), 0-based, pairs (2i, 2i + 1) for i : Fin n; reason: a relabelling of the indices
--   - encoding: log → Real.logb 2 (base 2); reason: the paper measures memory in bits; Real.logb 2 0 = 0 makes T = 0 harmless
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Result 1, p.2 (PDF p.4); final proof p.30 (PDF p.32)

import Mathlib
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_xorLift
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_successProb

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- Result 1 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.2 = PDF p.4): "For any XOR-function g : {0, 1}^{2n} → {0, 1} with sensitivity k,
any branching program that computes g in the random query model with probability of success at least
2/3 with width 2^S and time T must satisfy: T · (S + log T) = Ω(n · k)."

**Formalization Note** `g = xorLift f = f ∘ ⊕2` and `k = sens[g]`. `Ω` is one absolute constant
`c > 0` chosen before `n, f, S, T` and the program. The program is a randomized layered branching
program (a distribution on deterministic programs with `2^S` nodes per layer and `T` steps) reading
i.i.d. uniform samples `(i, y(i))`, `i ∈ [2n] = Fin (2 * n)`, with success probability at least `2/3`
on every input. `log` is base 2. -/
theorem result_1 : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (S T : ℕ)
      (μ : FinDist (DetBP (2 ^ S) (Fin (2 * n) × Bool) T)),
      (∀ y, (2 : ℝ) / 3 ≤ successProb μ (xorLift f) y) →
      c * n * sens (xorLift f) ≤ (T : ℝ) * (S + Real.logb 2 T) := by sorry

end RandomQueryXOR
