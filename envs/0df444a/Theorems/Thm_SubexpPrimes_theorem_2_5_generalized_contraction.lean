-- Prove2me | Theorems.Thm_SubexpPrimes_theorem_2_5_generalized_contraction
-- name    : SubexpPrimes.theorem_2_5_generalized_contraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:39.723746+00:00
-- url     : https://prove2.me/theorems/16a8b79b-271e-47cc-b9f7-807d34da0dac
-- title:
--   Theorem 2.5 — the generalized contraction lemma
-- statement:
--   Let $G$ have $m\ge2$ edges, maximum degree at most $m^{3/4}$, description length $L$, and uniform entry algorithms running in time $\mathrm{poly}(m+L)$. At $w$ designated vertices the entries lie in $2^{-p}\mathbb Z\cap[-1,1]$; all other entries lie in $\{0,1\}$. Given integers $p,\rho\ge0$ and $a$, with $w,p,|a|,\rho=O(m)$, one can deterministically compute $z\in2^{-(\rho+2)}\mathbb Z$ with
--
--   $$
--   \big|z-2^aZ(G)\big|\le2^{-\rho}
--   $$
--
--   in time $\mathrm{poly}(m+L)\,2^{O(m/\sqrt{\log m})}$ and space $\mathrm{poly}(m+L)$.
--
--   This is the only algorithmic primitive of the paper: every algorithm in it calls this theorem on networks with $O(n)$ edges and does only polynomial work besides.
--
--   **Formalization Note** The constants are fixed after the bound $c$ and the entry machine $E$, and before the instance, and an entry costs real machine steps. The degree bound keeps the printed constant $1$.
--
--   Differences from the source:
--   - reading: deterministically, in time and space → the published PrimitiveMachine with visitedSpace, which counts every tape including the input; reason: the paper names no machine model; this is the model of the platform's proved exact_count_and_sat, and any reasonable model states the same class of bound
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - encoding: given integers p, ρ and a → p as a field of the description, and a, ρ on the input after it; reason: the machine receives the same data
--   - encoding: z ∈ 2^{−(ρ+2)}ℤ → the integer k with z = k/2^{ρ+2}, sign bit then binary; reason: the same number
--   - encoding: uniform entry algorithms running in time poly(m + L) → the entry machine E runs within time and space c(m + L + 1)^c; reason: in the PrimitiveMachine model the visited space is at most the input length plus the number of tapes times (time + 1), and the inputs here have length polynomial in the same quantity, so a time bound gives the space bound with a larger constant; the constant is universally quantified, so no instance is lost
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 2.5, p.15; Theorem A.22, p.74

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_NetDesc_Evaluable

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 2.5 (Generalized contraction lemma)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.15; also Theorem A.22, p.74.

Let `G` have `m ≥ 2` edges, maximum degree at most `m^{3/4}`, description length `L`, and uniform
entry algorithms running in time `poly(m + L)`. At `w` designated vertices the entries lie in
`2^{-p}ℤ ∩ [-1, 1]`; all others lie in `{0, 1}`. Given integers `p, ρ ≥ 0` and `a`, with
`w, p, |a|, ρ = O(m)`, one can deterministically compute `z ∈ 2^{-(ρ+2)}ℤ` with
`|z - 2^a Z(G)| ≤ 2^{-ρ}` in time `poly(m + L) E(m)` and space `poly(m + L)`.

**Formalization Note.** `∀ c E ∃ A K ∀ instance`: the constants are fixed before the instance, and an
entry costs real machine steps. `p` is the field `prec` of the description, and `a`, `ρ` follow it on
the input. The output `z = k / 2^{ρ+2}` is the integer `k`. Isolated vertices and multi-edges are
allowed. The degree bound keeps the printed constant `1`. -/
theorem theorem_2_5_generalized_contraction :
    ∀ (c : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount),
    ∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (K : ℕ),
    ∀ (D : NetDesc) (T : D.Tables ℚ) (a : ℤ) (ρ : ℕ),
      D.Evaluable c E outE T → |a| ≤ c * D.m → ρ ≤ c * D.m →
      ∃ k : ℤ,
        |(k : ℚ) / 2 ^ (ρ + 2) - (2 : ℚ) ^ a * (D.net T).Z| ≤ (2 : ℚ) ^ (-(ρ : ℤ)) ∧
        RunsWithin A outA
          (Encoding.encodeList id [D.encode, intWord a, Encoding.encodeNat ρ])
          (intWord k)
          (subexpBound K (D.m + D.encode.length) D.m)
          (polyBound K (D.m + D.encode.length)) := by sorry

end SubexpPrimes
