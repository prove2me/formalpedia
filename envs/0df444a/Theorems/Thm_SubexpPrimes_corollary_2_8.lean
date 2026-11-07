-- Prove2me | Theorems.Thm_SubexpPrimes_corollary_2_8
-- name    : SubexpPrimes.corollary_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:48.692886+00:00
-- url     : https://prove2.me/theorems/6edeb510-4692-455f-a0c7-6aeb4fa10e72
-- title:
--   Corollary 2.8 — integers, zero tests and search
-- statement:
--   Let $A$ be within $\eta$ of a combination of contractions at scale $s$. The following hold, each in time $\mathrm{poly}(s+L)\,2^{O(s/\sqrt{\log s})}$ and polynomial space.
--
--   1. **Integers.** If $A$ is an integer and $\eta\le1/8$, then $A$ can be computed exactly.
--   2. **Zero tests.** If $A\ge0$, and either $A=0$ or $A\ge\delta$ for some $\delta\ge2^{-s}$ with $\eta\le\delta/8$, then one can decide whether $A=0$.
--   3. **Search.** Let $A=\sum_{x\in\{0,1\}^n}C(x)\omega(x)$ with weights $\omega(x)\ge0$, and suppose that for every prefix $\pi$ the sum restricted to the inputs that begin with $\pi$ is within $\eta$ of a combination of contractions at scale $s$ and satisfies the hypothesis of the zero test. Then one can find the least $x$ with $C(x)\omega(x)>0$, or report that none exists.
--
--   Over a correct zero-test oracle, the procedure of the search makes $n+1$ tests when some input qualifies and one test otherwise.
--
--   These are the three ways in which the paper turns approximate contractions into what it actually wants. In the proof of Theorem 1, $A=W_C$, $\delta=\ln2$, and the threshold is $1/4$.
--
--   **Formalization Note** One machine for the whole family, fixed after the family and before the index.
--
--   Differences from the source:
--   - reading: deterministically, in time and space → the published PrimitiveMachine with visitedSpace, which counts every tape including the input; reason: the paper names no machine model; this is the model of the platform's proved exact_count_and_sat, and any reasonable model states the same class of bound
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - reading: A ≥ δ for some δ ≥ 2^{−s} → the family also builds a dyadic threshold strictly between δ/4 and 3δ/4, and an accuracy k = O(s) with 2^{−k} ≤ δ/8; reason: the proof uses "a dyadic threshold in this range"; without one the statement is false for a fixed machine: with S = 1/4 and an undecidable set D, put A = 1/4, δ = 1/4, η = 0 on D and A = 0, δ = 2, η = 1/4 off D, and the test decides D. δ itself is not restricted
--   - reading: the hypothesis of (b) holds for C → the hypothesis holds for A, as the empty prefix of the family of restrictions; reason: C is not a quantity that (b) applies to; the proof tests A first
--   - reading: x ∈ {0,1}ⁿ, with n not bounded in the statement → n ≤ c(s + L + 1)^c, computed from the index in polynomial time; reason: otherwise printing x within the stated time is impossible; every use in the paper has n ≤ s
--   - reading: with n + 1 zero tests → at most n + 1 calls: exactly n + 1 if an input qualifies and one otherwise; reason: the proof stops after the first test when no input qualifies, so the printed number is the worst case
--   - reading: poly(s + L), with L the description length → L read as the length of the index word; reason: the builder runs in time polynomial in s and that length, so the descriptions are at most polynomially longer
--   - encoding: networks constructed in time poly(s + L), entry algorithms in time poly(m + L) → builder and entry machines bounded in time and space by one polynomial; reason: in the PrimitiveMachine model the visited space is at most the input length plus the number of tapes times (time + 1), and the inputs here have length polynomial in the same quantity, so a time bound gives the space bound with a larger constant; the constant is universally quantified, so no instance is lost
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Corollary 2.8, pp.16–17

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_CombTerm
import Definitions.Def_SubexpPrimes_prefixSearch

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Corollary 2.8 (Integers, zero tests, and search)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), pp.16–17.

Let `A` be within `η` of a combination of contractions at scale `s`, each part in time
`poly(s + L) E(cs)` and polynomial space. (a) If `A` is an integer and `η ≤ 1/8`, then `A` can be
computed exactly. (b) If `A ≥ 0`, and either `A = 0` or `A ≥ δ` for some `δ ≥ 2^{-s}` with
`η ≤ δ/8`, then one can decide whether `A = 0`. (c) Let `A = ∑_x C(x) ω(x)` with `ω ≥ 0`, with the
hypothesis of (b) for `A` and for every prefix restriction, each within `η` of a combination at scale
`s`. Then one can find the least `x` with `C(x) ω(x) > 0`, or report that none exists, with `n + 1`
zero tests.

**Formalization Note.** The machine is fixed after the family and before the index; `L` is the length
of the index word. In (b) and (c) the family also provides a dyadic threshold (`HasThreshold`), as in
the proof, because without it a fixed machine would decide an arbitrary set: take `S = 1/4` and, on
the set, `A = 1/4`, `δ = 1/4`, `η = 0`, and off it, `A = 0`, `δ = 2`, `η = 1/4`. In (c) the printed "the
hypothesis of (b) holds for C" means for `A`, which is the empty prefix; the input length `n` is given
in polynomial time and is at most polynomial, as it must be to print `x`. The prefix index is
`(a, π)` with `|π| ≤ n`. The last clause is the procedure over a correct zero-test oracle: `n + 1`
tests when some input qualifies, one test otherwise. -/
theorem corollary_2_8 :
    (∀ (α : Type) (enc : α → List Bool) (valid : α → Prop) (s : α → ℕ) (A η : α → ℝ),
      WithinCombination enc valid s A η →
      (∀ a, valid a → (∃ k : ℤ, A a = k) ∧ η a ≤ 1 / 8) →
      ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ a, valid a → ∃ k : ℤ, A a = k ∧
          RunsWithin M out (enc a) (intWord k)
            (subexpBound K (s a + (enc a).length) (s a))
            (polyBound K (s a + (enc a).length))) ∧
    (∀ (α : Type) (enc : α → List Bool) (valid : α → Prop) (s : α → ℕ) (A η δ : α → ℝ),
      WithinCombination enc valid s A η → HasThreshold enc valid s δ →
      (∀ a, valid a → ZeroTestHyp (A a) (δ a) (η a) (s a)) →
      ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ a, valid a → ∃ b : Bool, (b = true ↔ A a = 0) ∧
          RunsWithin M out (enc a) [b]
            (subexpBound K (s a + (enc a).length) (s a))
            (polyBound K (s a + (enc a).length))) ∧
    (∀ (α : Type) (enc : α → List Bool) (valid : α → Prop) (s n : α → ℕ)
        (C : α → List Bool → Prop) (ω : α → List Bool → ℝ)
        (η δ : α × List Bool → ℝ),
      (∀ a, valid a → ∀ x, 0 ≤ ω a x) →
      (∃ (B : PrimitiveMachine) (outB : Fin B.tapeCount) (c : ℕ), ∀ a, valid a →
        n a ≤ c * (s a + (enc a).length + 1) ^ c ∧
        RunsWithin B outB (enc a) (Encoding.encodeNat (n a))
          (polyBound c (s a + (enc a).length)) (polyBound c (s a + (enc a).length))) →
      (let encP := fun p : α × List Bool => Encoding.encodeList id [enc p.1, p.2]
       let validP := fun p : α × List Bool => valid p.1 ∧ p.2.length ≤ n p.1
       let sP := fun p : α × List Bool => s p.1
       let AP := fun p : α × List Bool => restrictedSum (n p.1) (C p.1) (ω p.1) p.2
       WithinCombination encP validP sP AP η →
       HasThreshold encP validP sP δ →
       (∀ p, validP p → ZeroTestHyp (AP p) (δ p) (η p) (sP p)) →
       ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ a, valid a → ∃ o : Option (List Bool),
          IsSearchAnswer (n a) (fun x => C a x ∧ 0 < ω a x) o ∧
          RunsWithin M out (enc a) (searchWord o)
            (subexpBound K (s a + (enc a).length) (s a))
            (polyBound K (s a + (enc a).length)))) ∧
    (∀ (n : ℕ) (q : List Bool → Prop) (z : List Bool → Bool),
      (∀ π : List Bool, π.length ≤ n →
        (z π = true ↔ ∀ x : List Bool, x.length = n → π <+: x → ¬ q x)) →
      IsSearchAnswer n q (prefixSearch n z).1 ∧
      (prefixSearch n z).2 ≤ n + 1 ∧
      ((prefixSearch n z).1.isSome → (prefixSearch n z).2 = n + 1)) := by sorry

end SubexpPrimes
