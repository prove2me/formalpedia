-- Prove2me | Theorems.Thm_SubexpPrimes_Supplement_theorem_3_arithmetic_search
-- name    : SubexpPrimes.Supplement.theorem_3_arithmetic_search
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:46:30.337096+00:00
-- url     : https://prove2.me/theorems/631898dc-e364-4eef-a9f6-e0967f1c9c21
-- title:
--   Theorem 3 — arithmetic search and counting under a circuit constraint in time $2^{O(m/\sqrt{\log m})}$
-- statement:
--   Let $C$ be a constraint on $n$-bit strings given by a fan-in-two Boolean circuit with $s$ gates, write $C(p)=1$ when the circuit accepts the $n$-bit string of $p$, and let $m=n+s$. Each of the following problems is solved by a single deterministic machine in time $2^{O(m/\sqrt{\log m})}$ and polynomial space (for problems without a circuit, $m=n$):
--
--   1. **Constrained primes.** Find the least prime $p<2^n$ with $C(p)=1$, or report that none exists. In particular, find the next prime after a given $n$-bit integer $N$, and decide whether a given interval $[a,b]$ with $a,b<2^n$ contains a prime.
--   2. **Prime pairs.** Given an interval $I=[a,b]\subseteq[1,2^n)$, find the least $p\in I$ with $p$ and $2p+1$ prime (the smallest Sophie Germain pair) and the least $p\in I$ with $p$ and $p+2$ prime (the smallest twin pair), each or report that none exists.
--   3. **Factoring.** Output the complete factorization of an $n$-bit integer $X\ge1$.
--   4. **Irreducibles over $\mathbb F_2$.** Output the number $I_n(C)$ of irreducible monic polynomials of degree $n$ over $\mathbb F_2$ whose $n$ free coefficients satisfy $C$, and the least one in coefficient order (or report that none exists).
--   5. **Roots modulo primes.** Fix $d\ge1$. Given a monic $f\in\mathbb Z[X]$ of degree $d$ with $O(n)$-bit coefficients and $r\le d$, find the least prime $p<2^n$ with $C(p)=1$ such that $f$ has exactly $r$ distinct roots modulo $p$, or report that none exists; here the machine and the constant in the exponent depend on $d$, so the time is $2^{O_d(m/\sqrt{\log m})}$.
--
--   Moreover, for a monic cubic $f$ and a prime $p$, $f$ has no root modulo $p$ if and only if $f$ is irreducible modulo $p$.
--
--   For circuits of size $O(n)$, such as prescribed binary digits, intervals and prefixes, all of these run in time $2^{O(n/\sqrt{\log n})}$; prior deterministic methods took time $2^{n(1-o(1))}$ or $2^{n/2}$ for most of them.
--
--   **Formalization Note** Time is $K(u+1)^K2^{Km/\sqrt{\log_2 m}}$ and space $K(u+1)^K$, with $u$ the input length and $K$ fixed before every input. Integers are given as $n$-bit strings, most significant bit first, and output in binary, least significant bit first; a circuit is given with $1^n$.
--
--   Differences from the source:
--   - encoding: time 2^{O(m/√log m)} → K (u+1)^K 2^{K m/√(log₂ m)} with u the input length; reason: for a circuit whose gates read existing wires u is polynomial in m, so the factor (u+1)^K is absorbed in 2^{O(m/√log m)} at m ≥ 2; the factor only keeps the bound meaningful at m ≤ 1 and for gate lists naming wires that do not exist, whose encodings are not bounded by any function of m
--   - encoding: polynomial space → at most K (u+1)^K visited cells at every step, input tape included; reason: the published RunsWithin counts the input tape; u is polynomial in m for the source's circuits
--   - reading: n-bit integer → n-bit string with leading zeros allowed (N, X, a, b < 2ⁿ); reason: the paper's notation, p.13: an n-bit string is read as an integer in [0, 2ⁿ), leading zeros allowed; this is the stronger reading
--   - reading: decide whether a given interval contains a prime → interval [a, b] with a, b < 2ⁿ given as n-bit strings (empty when a > b); reason: every interval of integers below 2ⁿ is [a, b] for such a, b
--   - reading: an interval I ⊆ [1, 2ⁿ) → I = [a, b] with 1 ≤ a ≤ b < 2ⁿ, given as n-bit strings; only p must lie in I; reason: every nonempty integer interval in [1, 2ⁿ) has this form; 2p+1 and p+2 may have n+1 bits (p.38)
--   - reading: the complete factorization of an n-bit integer → for 1 ≤ X < 2ⁿ, the list Nat.primeFactorsList X (nondecreasing, with multiplicity; empty for X = 1); reason: 0 has no factorization; X = 1 is the empty product
--   - encoding: monic f of degree d with O(n)-bit coefficients; fix d → for every d ≥ 1 and every c₀, one machine and constant for all f with natDegree d, monic, |coefficients| < 2^{c₀(n+1)}; reason: the O(n) constant is fixed together with d, as the source's O_d allows
--   - encoding: f has exactly r roots modulo p → rootCount f p = r, the number of u ∈ [0, p) with p ∣ f(u); reason: the source counts distinct roots in ℤ/pℤ (p.36: rp counts distinct roots)
--   - reading: for a cubic f and r = 0, these are the primes modulo which f is irreducible → for monic f of degree 3 and prime p: rootCount f p = 0 ↔ f mod p is irreducible in (ℤ/pℤ)[X]; reason: the bullet's f is monic; the remark is a statement about such f
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 3, pp.5–6 (PDF pp.7–8); proofs in §6 p.28, §7 pp.29–33, §8 pp.35–36, §9 p.38

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_RunsWithin
import Definitions.Def_SubexpPrimes_bitsToNat
import Definitions.Def_SubexpPrimes_Circuit
import Definitions.Def_SubexpPrimes_prefixSearch
import Definitions.Def_SubexpPrimes_Supplement_irrCount
import Definitions.Def_SubexpPrimes_Supplement_rootCount
import Definitions.Def_SubexpPrimes_Supplement_IsLeastOrNone

set_option autoImplicit false

namespace SubexpPrimes.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 3 (Arithmetic search and counting)** — Gajulapalli, *Deterministic Construction of
Primes in Subexponential Time* (manuscript, sha256 6ad4d3de…), pp.5–6.

Let `C` be a constraint given by a circuit `c` of size `s`, and let `m = n + s`. Each of the following
is solved by one deterministic machine in time `2^{O(m/√log m)}` and polynomial space:
1. *Constrained primes*: the least prime `p < 2ⁿ` with `C(p) = 1`, or "none"; in particular the next
   prime after a given `n`-bit integer, and whether a given interval contains a prime.
2. *Prime pairs*: for an interval `I = [a, b] ⊆ [1, 2ⁿ)`, the smallest Sophie Germain pair `(p, 2p+1)`
   and the smallest twin pair `(p, p+2)` with `p ∈ I`, each or "none".
3. *Factoring*: the complete factorization of an `n`-bit integer.
4. *Irreducibles over `F₂`*: the number of irreducible monic degree-`n` polynomials over `F₂` whose
   `n` free coefficients satisfy `C`, and the least one (or "none").
5. *Roots modulo primes*: for fixed `d ≥ 1`, monic `f ∈ ℤ[X]` of degree `d` with `O(n)`-bit coefficients
   and `r ≤ d`, the least prime `p < 2ⁿ` with `C(p) = 1` modulo which `f` has exactly `r` roots, or
   "none", in time `2^{O_d(m/√log m)}`. For a cubic `f` and `r = 0` these are the primes modulo which
   `f` is irreducible.

**Formalization Note.** A circuit is the published `Circuit` (a list of fan-in-two gates, size =
length); `C(p)` is `c.eval (bitsOf n p)`, the `n`-bit string of `p`, most significant bit first. A
circuit input is `(1ⁿ, encoding of c)`. Time is `subexpBound K u m = K (u+1)^K 2^{K m/√(log₂ m)}` with
`u` the input length (`= n` up to a constant for the inputs without a circuit, which take `m = n`) and
space `polyBound K u`; for a circuit whose gates read existing wires `u` is polynomial in `m`, so the
factor `(u+1)^K` is absorbed in `2^{O(m/√log m)}`. Integers are given as `n`-bit strings (leading zeros
allowed, p.13) and output as `countWord`; "or none" answers are `Option`s. In item 5 the machine and
`K` depend on `d` and on the constant `c₀` of "`O(n)` bits" (every coefficient below `2^{c₀(n+1)}` in
absolute value); `f` is given by its coefficient list and `r` in unary. The last conjunct is the
cubic remark: for a monic cubic, `r_p = 0` iff `f mod p` is irreducible. -/
theorem theorem_3_arithmetic_search :
    -- 1. constrained primes
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ (n : ℕ) (c : Circuit),
        let inp := Encoding.encodeList id [List.replicate n true, c.encode]
        ∃ o : Option ℕ,
          IsLeastOrNone {p : ℕ | p.Prime ∧ p < 2 ^ n ∧ c.eval (bitsOf n p) = true} o ∧
          RunsWithin M out inp (natOptWord o)
            (subexpBound K inp.length (n + c.length)) (polyBound K inp.length)) ∧
    -- 1'. the next prime after a given n-bit integer
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ n N : ℕ, N < 2 ^ n → ∃ p : ℕ,
        IsLeast {q : ℕ | q.Prime ∧ N < q} p ∧
        RunsWithin M out (bitsOf n N) (countWord p) (subexpBound K n n) (polyBound K n)) ∧
    -- 1''. whether a given interval contains a prime
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ n a b : ℕ, a < 2 ^ n → b < 2 ^ n → ∃ β : Bool,
        (β = true ↔ ∃ p : ℕ, p.Prime ∧ a ≤ p ∧ p ≤ b) ∧
        RunsWithin M out (Encoding.encodeList id [bitsOf n a, bitsOf n b]) [β]
          (subexpBound K n n) (polyBound K n)) ∧
    -- 2. prime pairs
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ n a b : ℕ, 1 ≤ a → a ≤ b → b < 2 ^ n → ∃ oSG oTw : Option ℕ,
        IsLeastOrNone {p : ℕ | a ≤ p ∧ p ≤ b ∧ p.Prime ∧ (2 * p + 1).Prime} oSG ∧
        IsLeastOrNone {p : ℕ | a ≤ p ∧ p ≤ b ∧ p.Prime ∧ (p + 2).Prime} oTw ∧
        RunsWithin M out (Encoding.encodeList id [bitsOf n a, bitsOf n b])
          (Encoding.encodeList id [natOptWord oSG, natOptWord oTw])
          (subexpBound K n n) (polyBound K n)) ∧
    -- 3. factoring
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ n X : ℕ, 1 ≤ X → X < 2 ^ n →
        RunsWithin M out (bitsOf n X) (Encoding.encodeList countWord X.primeFactorsList)
          (subexpBound K n n) (polyBound K n)) ∧
    -- 4. irreducibles over F₂: the count and the least one
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ (n : ℕ) (c : Circuit),
        let inp := Encoding.encodeList id [List.replicate n true, c.encode]
        ∃ o : Option (List Bool),
          IsSearchAnswer n (IrrAccepted (fun x => c.eval x = true)) o ∧
          RunsWithin M out inp
            (Encoding.encodeList id
              [countWord (irrCount n (fun x => c.eval x = true)), searchWord o])
            (subexpBound K inp.length (n + c.length)) (polyBound K inp.length)) ∧
    -- 5. roots of polynomials modulo primes
    (∀ d : ℕ, 1 ≤ d → ∀ c₀ : ℕ,
      ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
        ∀ (n : ℕ) (c : Circuit) (f : Polynomial ℤ) (r : ℕ),
          f.Monic → f.natDegree = d → (∀ i : ℕ, |f.coeff i| < 2 ^ (c₀ * (n + 1))) → r ≤ d →
          let inp := Encoding.encodeList id
            [List.replicate n true, c.encode, coeffWord f, Encoding.encodeNat r]
          ∃ o : Option ℕ,
            IsLeastOrNone
              {p : ℕ | p.Prime ∧ p < 2 ^ n ∧ c.eval (bitsOf n p) = true ∧ rootCount f p = r} o ∧
            RunsWithin M out inp (natOptWord o)
              (subexpBound K inp.length (n + c.length)) (polyBound K inp.length)) ∧
    -- the cubic remark
    (∀ (f : Polynomial ℤ) (p : ℕ), p.Prime → f.Monic → f.natDegree = 3 →
      (rootCount f p = 0 ↔ Irreducible (f.map (Int.castRingHom (ZMod p))))) := by sorry

end SubexpPrimes.Supplement
