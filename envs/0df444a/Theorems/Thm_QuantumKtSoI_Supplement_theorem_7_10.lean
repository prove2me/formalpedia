-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_7_10
-- name    : QuantumKtSoI.Supplement.theorem_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:46:29.114879+00:00
-- url     : https://prove2.me/theorems/bab3e455-8f6d-4db3-af30-3da86f015e27
-- title:
--   Theorem 7.10, p.110 — near-full gaps $g\ge C_*$: a promise algorithm in time $2^{O(\mathrm{bud}(\lambda)+\log(\lambda+2))}$ and a consistent total language with advice
-- statement:
--   There is an integer $C_*\ge1$ such that the following holds. Let $g:\mathbb N\to\mathbb N$ be computable in time polynomial in the value of its argument with $g(\lambda)\ge C_*$ for all sufficiently large $\lambda$, and let $\mathrm{bud}(\lambda)=\max\{0,B(\lambda)-g(\lambda)\}$ and $\widehat{\mathrm{bud}}(N)=\max(\{\mathrm{bud}(\ell):1\le\ell\le N,\nu(\ell)=N\}\cup\{0\})$.
--
--   1. There is a machine that, for every sufficiently large $\lambda$, solves the gap-$g$ promise problem at length $\lambda$ in time $2^{O(\mathrm{bud}(\lambda)+\log(\lambda+2))}$.
--   2. There is a total language $L$ consistent with the gap $g$ that has a bounded-error quantum algorithm with advice of length $O(\widehat{\mathrm{bud}}(N)+\log(N+2))$ and all-branch running time $2^{O(\widehat{\mathrm{bud}}(N)+\log(N+2))}$ on inputs of length $N$.
--   3. In particular, $g(\lambda)=\lambda$ gives a uniform polynomial-time promise algorithm and a consistent total language in $\mathrm{BQP}/O(\log N)$.
--
--   The constants implied by $O(\cdot)$ may depend on $g$; the integer $C_*$ does not.
--
--   This shows that the lower bound of Theorem 7.3 cannot extend to gaps close to the full length.
--
--   **Formalization Note** $B(\lambda)=\lambda+\lfloor2\log(\lambda+1)\rfloor+7+\lceil\log(\lambda+1)\rceil$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - reading: g computable in time polynomial in the value of its argument (no input format named) → a deterministic coded machine on input b(λ) halts within c(λ+2)^k steps with output b(g(λ)); reason: with a bound polynomial in the value λ, unary and binary inputs give the same class
--   - reading: 2^{O(·)} time and O(·) advice bounds whose constants may depend on g → one real constant K per clause, chosen after g; reason: the paper states that the implied constants may depend on g and the machine model
--   - reading: advice supplied as in the definition of BQP/f: strings a_N with |a_N| = f(N), inputs ⟨x, a_N⟩ → a function adv with |adv(N)| ≤ K(b̂ud(N)+log(N+2)); the machine runs on ⟨x, adv(|x|)⟩ for all large |x|; reason: take f(N) = |adv(N)|, which is O(·) of the stated bound
--   - reading: "a uniform polynomial-time promise algorithm" and "BQP/O(log N)" for g(λ) = λ → time c(ν(λ)+2)^k on queries, time c(N+2)^k with advice of length ≤ K log(N+2); reason: polynomial in the input length, which for a query is ν(λ)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 7.10, p.110; B(λ), p.104; gap promise problem, p.96; BQP/f, pp.22–23

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_query
import Definitions.Def_QuantumKtSoI_Supplement_PolyInValue
import Definitions.Def_QuantumKtSoI_Supplement_bud

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 7.10** (Near-full gaps; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.110). There is an integer `C∗ ≥ 1` such that the
following holds. Let `g : ℕ → ℕ` be computable in time polynomial in the value of its argument with
`g(λ) ≥ C∗` for all large `λ`. (i) There is a machine that, for every sufficiently large `λ`, solves
the gap-`g` promise problem at length `λ` in time `2^{O(bud(λ)+log(λ+2))}`. (ii) There is a total
language `L` consistent with the gap `g` that has a bounded-error quantum algorithm with advice of
length `O(b̂ud(N) + log(N+2))` and all-branch running time `2^{O(b̂ud(N)+log(N+2))}` on inputs of
length `N`, the advice supplied as in BQP/f. The `O(·)` constants may depend on `g`; `C∗` does not.
In particular, `g(λ) = λ` gives a uniform polynomial-time promise algorithm and a consistent total
language in BQP/O(log N).

**Formalization Note** The `O(·)` bounds are existential constants `K` chosen after `g`.
Advice (p.22): strings `a_N` given with the input as `⟨x, a_{|x|}⟩`; the machine halts on every
branch within the time bound and accepts members with probability `≥ 2/3` and nonmembers with
probability `≤ 1/3`, for all large `N`; an advice length `|a_N| ≤ K(⋯)` is the paper's
`|a_N| = f(N)` with `f = O(⋯)` (take `f(N) = |a_N|`). Real deadlines are read as `⌊·⌋`. Polynomial
time is `c(m+2)^k` in the input length `m` (`ν(λ)` for queries). `bud`, `b̂ud` are those of p.110
for `B(λ)` of p.104; queries, consistency and solving at a length are those of §6.6 for
`µ(x) = qKt(x)`. `G` is any admissible glue routine set (p.24). -/
theorem theorem_7_10 (G : GlueRoutines) (hG : G.Admissible) :
    ∃ Cstar : ℕ, 1 ≤ Cstar ∧
      (∀ g : ℕ → ℕ, PolyInValue g → (∃ l₀ : ℕ, ∀ lam ≥ l₀, Cstar ≤ g lam) →
        (∃ K : ℝ, ∃ A : CodedMachine, A.Valid ∧ ∃ l₀ : ℕ, ∀ lam ≥ l₀,
          SolvesGapAt (fun x => (qKt G x [] : ℝ)) A g lam
            ((2 : ℝ) ^ (K * ((bud g lam : ℝ) + Real.logb 2 ((lam : ℝ) + 2))))) ∧
        ∃ L : Set (List Bool), ConsistentGap (fun x => (qKt G x [] : ℝ)) g L ∧
          ∃ K : ℝ, ∃ adv : ℕ → List Bool,
            (∀ N : ℕ, ((adv N).length : ℝ) ≤ K * ((budHat g N : ℝ) + Real.logb 2 ((N : ℝ) + 2))) ∧
            ∃ A : CodedMachine, A.Valid ∧ ∃ n₀ : ℕ, ∀ x : List Bool, n₀ ≤ x.length →
              A.toMachine.HaltsWithin (pair x (adv x.length))
                  ⌊(2 : ℝ) ^ (K * ((budHat g x.length : ℝ) + Real.logb 2 ((x.length : ℝ) + 2)))⌋₊ ∧
                (x ∈ L → (2 / 3 : ℝ) ≤ A.toMachine.outputProb (pair x (adv x.length))
                  ⌊(2 : ℝ) ^ (K * ((budHat g x.length : ℝ) + Real.logb 2 ((x.length : ℝ) + 2)))⌋₊
                  [true]) ∧
                (x ∉ L → A.toMachine.outputProb (pair x (adv x.length))
                  ⌊(2 : ℝ) ^ (K * ((budHat g x.length : ℝ) + Real.logb 2 ((x.length : ℝ) + 2)))⌋₊
                  [true] ≤ 1 / 3)) ∧
      (∃ A : CodedMachine, A.Valid ∧ ∃ c k l₀ : ℕ, ∀ lam ≥ l₀,
        SolvesGapAt (fun x => (qKt G x [] : ℝ)) A id lam ((c * (nu lam + 2) ^ k : ℕ) : ℝ)) ∧
      ∃ L : Set (List Bool), ConsistentGap (fun x => (qKt G x [] : ℝ)) id L ∧
        ∃ K : ℝ, ∃ adv : ℕ → List Bool,
          (∀ N : ℕ, ((adv N).length : ℝ) ≤ K * Real.logb 2 ((N : ℝ) + 2)) ∧
          ∃ A : CodedMachine, A.Valid ∧ ∃ c k n₀ : ℕ, ∀ x : List Bool, n₀ ≤ x.length →
            A.toMachine.HaltsWithin (pair x (adv x.length)) (c * (x.length + 2) ^ k) ∧
              (x ∈ L → (2 / 3 : ℝ) ≤
                A.toMachine.outputProb (pair x (adv x.length)) (c * (x.length + 2) ^ k) [true]) ∧
              (x ∉ L →
                A.toMachine.outputProb (pair x (adv x.length)) (c * (x.length + 2) ^ k) [true] ≤ 1 / 3) := by sorry

end QuantumKtSoI.Supplement
