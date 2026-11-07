-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_A_23_polynomial_tables
-- name    : SubexpPrimes.lemma_A_23_polynomial_tables
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:19.463063+00:00
-- url     : https://prove2.me/theorems/2bfd213b-1b81-46a9-9441-00674c1156f7
-- title:
--   Lemma A.23 — the contraction lemma with table values in $R_{P,\ell}$
-- statement:
--   Theorem A.2 holds for networks whose table values lie in $R_{P,\ell}=(\mathbb Z/2^P\mathbb Z)[V]/(V^\ell)$ with $1\le P,\ell=O(s)$. For every constant $c$ and every entry machine $E$ there are a machine $A$ and a constant $C$ such that the following holds for every instance with scale $s$ and input length $N$. If the network has at most $cs$ edges and maximum degree at most $cs^{9/10}$, $1\le P,\ell\le cs$, and the entries are computed by $E$ in time $c(N+s+1)^c2^{cs^{9/10}}$ and space $c(N+s+1)^c$, then $A$ outputs $Z(G)\in R_{P,\ell}$ in time
--
--   $$
--   C(N+s+1)^C\,2^{Cs/\sqrt{\log_2(s+2)}}
--   $$
--
--   and in space $C(N+s+1)^C$.
--
--   The entries of $R_{P,\ell}$ carry binary digits as powers of $V$, which is how real weights reach a lemma about integers. Its proof is the contraction lemma of OpenAI, carried coefficientwise.
--
--   Differences from the source:
--   - reading: deterministically, in time and space → the published PrimitiveMachine with visitedSpace, which counts every tape including the input; reason: the paper names no machine model; this is the model of the platform's proved exact_count_and_sat, and any reasonable model states the same class of bound
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - encoding: log s → log₂(s + 2); reason: s may be 1, where log₂ s = 0 is a junk value; the two agree up to the constant C for s ≥ 2
--   - encoding: R_{P,ℓ} as lists of ℓ integers modulo 2^P → polynomials over ZMod (2^P), read through their ℓ low coefficients; reason: truncation is a ring homomorphism, so the same element of R_{P,ℓ} results
--   - reading: a description of length poly(N + s) → the explicit edge list as part of the input; reason: the paper leaves the encoding open, and this is a description of that length
--   - reading: 1 ≤ P, ℓ = O(s) → 1 ≤ P, 1 ≤ ℓ, and P, ℓ ≤ cs; reason: the printed "1 ≤ P, ℓ" lists both parameters; at ℓ = 0 the ring R_{P,0} is zero and the instance is trivial
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma A.23, p.74; Theorem A.2, p.43

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_PolyInstance

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Lemma A.23 (Polynomial tables)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.74.

Theorem A.2 (p.43) holds for networks whose table values lie in `R_{P,ℓ}` with `1 ≤ P, ℓ = O(s)`:
for every `c` and every entry machine `E` there are a machine `A` and a constant `C` such that, for
every instance with at most `c s` edges, maximum degree at most `c s^{9/10}`, `1 ≤ P, ℓ ≤ c s`, and
tables computed by `E` in time `c (N+s+1)^c 2^{c s^{9/10}}` and space `c (N+s+1)^c`, the machine `A`
outputs `Z(G) ∈ R_{P,ℓ}` in time `C (N+s+1)^C 2^{C s/√(log₂(s+2))}` and space `C (N+s+1)^C`.

**Formalization Note.** The bound uses `log₂(s + 2)` because `s` may be `1`, where `log₂ s = 0`; this
is the paper's `f(u) = u/√log(u+2)` in the companion statement. `N` is the length of the encoded
instance. -/
theorem lemma_A_23_polynomial_tables :
    ∀ (c : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount),
    ∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (C : ℕ),
    ∀ (I : PolyInstance) (T : I.D.Tables (TruncPoly I.P)),
      1 ≤ I.P → I.P ≤ c * I.s → 1 ≤ I.ℓ → I.ℓ ≤ c * I.s → I.D.m ≤ c * I.s →
      (I.D.maxDeg : ℝ) ≤ c * (I.s : ℝ) ^ ((9 : ℝ) / 10) →
      I.EntryComputes E outE T
        (c * ((I.encode.length : ℝ) + I.s + 1) ^ c * (2 : ℝ) ^ (c * (I.s : ℝ) ^ ((9 : ℝ) / 10)))
        (c * ((I.encode.length : ℝ) + I.s + 1) ^ c) →
      RunsWithin A outA I.encode (truncWord I.ℓ (I.D.net T).Z)
        (C * ((I.encode.length : ℝ) + I.s + 1) ^ C *
          (2 : ℝ) ^ (C * (I.s : ℝ) / Real.sqrt (Real.logb 2 ((I.s : ℝ) + 2))))
        (C * ((I.encode.length : ℝ) + I.s + 1) ^ C) := by sorry

end SubexpPrimes
