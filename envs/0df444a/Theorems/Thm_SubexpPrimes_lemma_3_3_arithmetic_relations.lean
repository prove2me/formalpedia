-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_3_3_arithmetic_relations
-- name    : SubexpPrimes.lemma_3_3_arithmetic_relations
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:38.337272+00:00
-- url     : https://prove2.me/theorems/70954db0-af6c-4891-be70-54fdabb1b5bb
-- title:
--   Lemma 3.3 — arithmetic relations, powering, circuits and composition
-- statement:
--   On nonnegative integers of $n$ bits, the following relations have explicit functional representations with $O(n)$ edges and degree $O(n^{3/4})$:
--
--   1. addition and comparison;
--   2. division with remainder, $A=uy+r$ with $0\le r<u$;
--   3. modular multiplication, $uv\equiv c\pmod p$ with $0\le u,v,c<p$;
--   4. powering, $m=a^e$, for $e\ge1$ and a $k$-bit base $a$, with $O(ek)$ edges and degree $O((ek)^{3/4})$ uniformly in $e$ and $k$.
--
--   The same holds over $\mathbb F_2[X]$, with degrees in place of bit lengths. A circuit with $s$ gates on $n$ inputs has a functional representation with $O(n+s)$ edges and constant degree. Two functional representations compose along shared and hidden words: if the hidden word is determined by the outer inputs, the result is a functional representation of the conjunction over that word, with $O(1)$ further edges per wire read and degree at most the larger of the two degrees and $3$.
--
--   These relations carry every identity of the paper, each without counting anything twice.
--
--   Differences from the source:
--   - reading: there is a network → an explicit family: one builder machine, one entry machine, one constant, all polynomial; reason: Definition 2.3 and p.28 ("the arithmetic parts are explicit, and the rotation constants take time poly(p)") claim it, and Theorem 2.5 evaluates only such networks; this is the stronger reading and it implies the bare existence
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - encoding: relations on integers and polynomials → predicates on one list of input bits, read off by slices, most significant bit first; reason: the convention of p.13; a word of fixed width stands for one integer
--   - reading: nonnegative integers of O(n) bits → words of width n; reason: n rescales, so one constant before n is the same statement
--   - reading: a fixed e ≥ 1 → a given e, with constants uniform in e and k; reason: Lemma 5.3 uses the relation for every e ≤ n; this is the stronger reading
--   - reading: a constant number of these relations can be composed within the same bounds → a binary closure over wirings, stated for networks, iterated a constant number of times; reason: the paper states the rule of composition on p.20; the uniform closure is in the admissibility milestone
--   - reading: comparison over F₂[X] → comparison of coefficient words, which is the integer relation already stated; reason: the paper gives no other order on polynomials; a separate item would repeat the same predicate
--   - generalization: a circuit of O(n) gates → a circuit with any number s of gates, with O(n + s) edges and constant degree; reason: this is the example of p.14; at s = O(n) it gives the source's bound
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 3.3, p.19; §2.1, p.14; proof of Lemma 3.3, p.20

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_ExplicitFamily
import Definitions.Def_SubexpPrimes_bitsToNat
import Definitions.Def_SubexpPrimes_Circuit

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Lemma 3.3 (Arithmetic relations)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.19.

On `n`-bit words, explicit functional representations with `O(n)` edges and degree `O(n^{3/4})`:
(a) addition `x + y = z` and comparison `x ≤ y`, `x < y`; (b) division with remainder `A = uy + r`,
`0 ≤ r < u`; (c) modular multiplication `uv ≡ c (mod p)`, `0 ≤ u, v, c < p`; (d) powering `m = a^e`,
with `O(ek)` edges and degree `O((ek)^{3/4})`, uniformly in `e ≥ 1` and `k ≥ 1`, for a `k`-bit `a` and
an `ek`-bit `m`. The same over `F₂[X]`: `A + B = C`; `A = UY + R` with `deg R < deg U`;
`UV ≡ C (mod P)` with `deg U, deg V, deg C < deg P`; `M = A^e`. A circuit with `s` gates on `n` input
wires has a functional representation with `O(n + s)` edges and constant degree. Two functional
representations compose along shared and hidden wires: if the hidden word is determined by the
outer inputs, the result is a functional representation of the existential conjunction, with
`O(1)` further edges per wire read, and degree at most the larger degree and `3`.

**Formalization Note.** "`O(n)` bits" is one constant before `n`, so word width `n` loses nothing,
since `n` rescales. "For a fixed `e`" means a given `e`: the constants are uniform in `e`, which is
how Lemma 5.3 uses it, for every `e ≤ n`. Over `F₂[X]`, comparison is the comparison of coefficient
words, which is the integer relation stated in (a). "A constant number" is iterated binary
composition, and a wire is `Sum.inl i` for the outer bit `i` or `Sum.inr i` for the hidden bit `i`. -/
theorem lemma_3_3_arithmetic_relations :
    (HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n) (fun n => 3 * n)
      (fun n x => bitsToNat (slice x 0 n) + bitsToNat (slice x n n) =
        bitsToNat (slice x (2 * n) n))) ∧
    (HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n) (fun n => 2 * n)
      (fun n x => bitsToNat (slice x 0 n) ≤ bitsToNat (slice x n n))) ∧
    (HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n) (fun n => 2 * n)
      (fun n x => bitsToNat (slice x 0 n) < bitsToNat (slice x n n))) ∧
    (HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n) (fun n => 4 * n)
      (fun n x => bitsToNat (slice x 0 n) =
          bitsToNat (slice x n n) * bitsToNat (slice x (2 * n) n) + bitsToNat (slice x (3 * n) n) ∧
        bitsToNat (slice x (3 * n) n) < bitsToNat (slice x n n))) ∧
    (HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n) (fun n => 4 * n)
      (fun n x => bitsToNat (slice x 0 n) < bitsToNat (slice x (3 * n) n) ∧
        bitsToNat (slice x n n) < bitsToNat (slice x (3 * n) n) ∧
        bitsToNat (slice x (2 * n) n) < bitsToNat (slice x (3 * n) n) ∧
        (bitsToNat (slice x 0 n) * bitsToNat (slice x n n)) ≡
          bitsToNat (slice x (2 * n) n) [MOD bitsToNat (slice x (3 * n) n)])) ∧
    (HasLinearRep
      (fun p : ℕ × ℕ => Encoding.encodeList id [List.replicate p.1 true, List.replicate p.2 true])
      (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2) (fun p => p.1 * p.2) (fun p => p.2 + p.1 * p.2)
      (fun p x => bitsToNat (slice x p.2 (p.1 * p.2)) = bitsToNat (slice x 0 p.2) ^ p.1)) ∧
    (HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n) (fun n => 3 * n)
      (fun n x => polyOf (slice x 0 n) + polyOf (slice x n n) = polyOf (slice x (2 * n) n))) ∧
    (HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n) (fun n => 4 * n)
      (fun n x => polyOf (slice x 0 n) =
          polyOf (slice x n n) * polyOf (slice x (2 * n) n) + polyOf (slice x (3 * n) n) ∧
        (polyOf (slice x (3 * n) n)).degree < (polyOf (slice x n n)).degree)) ∧
    (HasLinearRep (fun n : ℕ => List.replicate n true) (fun n => 1 ≤ n) (fun n => n) (fun n => 4 * n)
      (fun n x => (polyOf (slice x 0 n)).degree < (polyOf (slice x (3 * n) n)).degree ∧
        (polyOf (slice x n n)).degree < (polyOf (slice x (3 * n) n)).degree ∧
        (polyOf (slice x (2 * n) n)).degree < (polyOf (slice x (3 * n) n)).degree ∧
        polyOf (slice x (3 * n) n) ∣
          polyOf (slice x 0 n) * polyOf (slice x n n) - polyOf (slice x (2 * n) n))) ∧
    (HasLinearRep
      (fun p : ℕ × ℕ => Encoding.encodeList id [List.replicate p.1 true, List.replicate p.2 true])
      (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2) (fun p => p.1 * p.2) (fun p => p.2 + p.1 * p.2)
      (fun p x => polyOf (slice x p.2 (p.1 * p.2)) = polyOf (slice x 0 p.2) ^ p.1)) ∧
    (∃ K : ℕ, ∀ (n : ℕ) (c : Circuit), ∃ (D : NetDesc) (T : D.Tables ℚ),
      D.inputs.length = n ∧ D.m ≤ K * (n + c.length) ∧ D.maxDeg ≤ K ∧
      IsFunctionalRep (D.net T) D.inputs (fun x => c.eval x = true)) ∧
    (∃ K : ℕ, ∀ (D₁ D₂ : NetDesc) (T₁ : D₁.Tables ℚ) (T₂ : D₂.Tables ℚ)
        (P₁ P₂ : List Bool → Prop) (k h : ℕ) (σ₁ σ₂ : List (ℕ ⊕ ℕ)),
      IsFunctionalRep (D₁.net T₁) D₁.inputs P₁ → IsFunctionalRep (D₂.net T₂) D₂.inputs P₂ →
      σ₁.length = D₁.inputs.length → σ₂.length = D₂.inputs.length →
      (∀ s ∈ σ₁ ++ σ₂, Sum.elim (· < k) (· < h) s) →
      (let read := fun (σ : List (ℕ ⊕ ℕ)) (a w : List Bool) =>
          σ.map (Sum.elim (fun i => a.getD i false) (fun i => w.getD i false))
       (∀ a w w' : List Bool, a.length = k → w.length = h → w'.length = h →
          P₁ (read σ₁ a w) → P₂ (read σ₂ a w) → P₁ (read σ₁ a w') → P₂ (read σ₂ a w') → w = w') →
       ∃ (D : NetDesc) (T : D.Tables ℚ),
        D.inputs.length = k ∧
        D.m ≤ D₁.m + D₂.m + K * (k + h + σ₁.length + σ₂.length) ∧
        D.maxDeg ≤ max (max D₁.maxDeg D₂.maxDeg) 3 ∧
        IsFunctionalRep (D.net T) D.inputs (fun a =>
          ∃ w : List Bool, w.length = h ∧ P₁ (read σ₁ a w) ∧ P₂ (read σ₂ a w)))) := by sorry

end SubexpPrimes
