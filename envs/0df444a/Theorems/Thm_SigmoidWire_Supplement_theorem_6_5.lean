-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_6_5
-- name    : SigmoidWire.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:46:06.870513+00:00
-- url     : https://prove2.me/theorems/c5761f6b-9423-4bfe-aeef-3569d2f61339
-- title:
--   Theorem 6.5 — a depth-two sigmoid circuit computing selection with zero separation has $m$ gates with $n\le 2m\log(12m)$
-- statement:
--   Let $n=2^k$ and let $C$ be a sigmoidal circuit of depth at most two, with arbitrary real weights and biases, that computes the selection function $f_n$ with zero separation. Then the number $m$ of gates of $C$ (the output gate included) satisfies
--   $$n\ \le\ 2m\log_2(12m).$$
--   In particular there is an absolute constant $c>0$ with $m\ge c\,n/\log_2 n$ for every $n\ge2$.
--
--   This $\Omega(n/\log n)$ gate lower bound holds with no restriction on the weights, in contrast with the polynomial-weight lower bounds of §5.
--
--   Differences from the source:
--   - encoding: n is a power of 2; inputs x ∈ {0,1}^{log n}, y ∈ {0,1}^n → n = 2^k for every k; the circuit has k + 2^k inputs, x first; x is read least significant bit first; reason: §6.2 assumes n a power of 2; the bit order changes nothing (a permutation of inputs)
--   - reading: an arbitrary depth-2 sigmoid circuit → depth ≤ 2 measured at the output; the output may read inputs directly; arbitrary real weights and biases; reason: the proof (p.41) allows direct input wires to the output and deletes gates off the output paths
--   - encoding: the number m of gates; log → m = C.size + 1, all gates; log base 2; reason: §6.2 takes logarithms in base 2
--   - encoding: m = Ω(n/ log n) → ∃ c > 0 ∀ k ≥ 1: c·n/log₂ n ≤ m; reason: the standard meaning; n ≥ 2 so that log₂ n > 0
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 6.5, p.41

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_selFn

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Theorem 6.5 (gate lower bound for selection at depth two, unrestricted weights).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 6.5, p.41 (PDF p.43): "Let C be an arbitrary depth-2 sigmoid circuit (with no
restriction on the weights) that computes the selection Boolean function f_n with zero separation.
Then the number m of gates in C satisfies n ≤ 2m log(12m); in particular, m = Ω(n/ log n)."

**Formalization Note.** `n = 2^k` (§6.2 assumes `n` is a power of `2`; logarithms are base `2`),
the circuit has `k + 2^k` inputs, depth at most `2` (measured at the output; the output may read
inputs directly), arbitrary real weights, and `m = C.size + 1` gates including the output.
Conjunct 1 is the exact inequality; conjunct 2 is "`m = Ω(n/log n)`" as `m ≥ c·n/log₂ n` for every
`n ≥ 2`, with one constant `c > 0`. -/
theorem theorem_6_5 :
    (∀ (k : ℕ) (C : Circuit (k + 2 ^ k)), C.depth ≤ 2 → ComputesSep Real.sigmoid C (selFn k) 0 →
      ((2 ^ k : ℕ) : ℝ) ≤ 2 * ((C.size + 1 : ℕ) : ℝ) * Real.logb 2 (12 * ((C.size + 1 : ℕ) : ℝ))) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 1 ≤ k → ∀ C : Circuit (k + 2 ^ k), C.depth ≤ 2 →
      ComputesSep Real.sigmoid C (selFn k) 0 →
        c * ((2 ^ k : ℕ) : ℝ) / Real.logb 2 ((2 ^ k : ℕ) : ℝ) ≤ ((C.size + 1 : ℕ) : ℝ)) := by sorry

end SigmoidWire.Supplement
