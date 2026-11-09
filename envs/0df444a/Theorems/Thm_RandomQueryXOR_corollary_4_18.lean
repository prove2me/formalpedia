-- Prove2me | Theorems.Thm_RandomQueryXOR_corollary_4_18
-- name    : RandomQueryXOR.corollary_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:11:58.250394+00:00
-- url     : https://prove2.me/theorems/74a3ca6d-ed0c-4208-9cc9-b670454411a3
-- title:
--   Corollary 4.18 — under Assumption 4.2, $T(S+\log T)=\Omega(n\cdot\mathrm{sens}[f])$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $f:\{0,1\}^n\to\{0,1\}$ satisfy Assumption 4.2: some input $x^\star$ with $\mathrm{sens}[f,x^\star]=\mathrm{sens}[f]$ has $\mathrm{sens}_0[f,x^\star]\ge\mathrm{sens}_1[f,x^\star]$. If a randomized branching program of length $T$ and width $2^S$ computes $g_{f\oplus}=f\circ\oplus_2$ in the random query model with probability of success at least $2/3$ on every input, then
--   $$
--   T\cdot(S+\log_2T)\ \ge\ c\cdot n\cdot\mathrm{sens}[f].
--   $$
--
--   This is Result 1 for functions whose most sensitive input has at least as many sensitive zeros as ones; negating the input removes the assumption.
--
--   Differences from the source:
--   - reading: f where Assumption 4.2 holds (x⋆_f an input with sens[f] = sens[f, x⋆_f]; we assume sens0[f, x⋆_f] ≥ sens1[f, x⋆_f]) → ∃ x⋆, sens[f, x⋆] = sens[f] ∧ sens1[f, x⋆] ≤ sens0[f, x⋆]; reason: the assumption fixes one maximum-sensitivity input; the existential hypothesis is the weaker one, so the theorem is the stronger reading
--   - reading: T · (S + log T) = Ω(·) → ∃ c > 0, chosen before n, f, S, T and the program, with c · (·) ≤ T · (S + log₂ T) for all of them; reason: the uniform reading of Ω; for the finitely many small n not covered by the proof's 'sufficiently large n', a correct program for non-constant g has T ≥ 1 and S ≥ 1, so a smaller c covers them
--   - encoding: a randomized branching program: a distribution D^A_n on programs with per-node distributions over outgoing edges → a probability distribution (WildeQIT.FinDist) on deterministic layered programs DetBP (2^S) _ T; reason: a run visits one node per layer, so independent per-node edge choices fold into a distribution on deterministic programs; the paper does the same in π_two step (ii)
--   - encoding: probability of success at least 2/3, the minimum over inputs → 2/3 ≤ success probability on every input y; reason: a lower bound on a minimum is a lower bound at every input
--   - encoding: [2n] with pairs (2i − 1, 2i) → Fin (2 * n), 0-based, pairs (2i, 2i + 1) for i : Fin n; reason: a relabelling of the indices
--   - encoding: log → Real.logb 2 (base 2); reason: the paper measures memory in bits; Real.logb 2 0 = 0 makes T = 0 harmless
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Corollary 4.18, p.29 (PDF p.31); Assumption 4.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_xorLift
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_successProb

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- Corollary 4.18 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.29 = PDF p.31): "For any function f : {0, 1}^n → {0, 1} where Assumption
4.2 holds, if a randomized branching program P computes g_{f⊕} with probability of success at least
2/3 with length T and width 2^S, then, T · (S + log T) = Ω(n · sens[f])."

**Formalization Note** Assumption 4.2 (p.16 = PDF p.18) is read as: some input `x⋆` with
`sens[f, x⋆] = sens[f]` has `sens0[f, x⋆] ≥ sens1[f, x⋆]`. `Ω` is one absolute constant `c > 0`
chosen before `n, f, S, T` and the program. `P` is a randomized program in the random query model
over `[2n] = Fin (2 * n)` with success at least `2/3` on every input; `log` is base 2. -/
theorem corollary_4_18 : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (S T : ℕ)
      (μ : FinDist (DetBP (2 ^ S) (Fin (2 * n) × Bool) T)),
      (∃ xs : Fin n → Bool, sensAt f xs = sens f ∧ sens1At f xs ≤ sens0At f xs) →
      (∀ y, (2 : ℝ) / 3 ≤ successProb μ (xorLift f) y) →
      c * n * sens f ≤ (T : ℝ) * (S + Real.logb 2 T) := by sorry

end RandomQueryXOR
