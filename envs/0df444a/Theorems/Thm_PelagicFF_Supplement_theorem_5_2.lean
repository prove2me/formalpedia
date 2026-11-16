-- Prove2me | Theorems.Thm_PelagicFF_Supplement_theorem_5_2
-- name    : PelagicFF.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:29:24.589216+00:00
-- url     : https://prove2.me/theorems/30e1d6f5-dff1-4d93-970c-d97a79fc3489
-- title:
--   Theorem 5.2 — $\mathrm{APFF}_n$: $n$ qubits one-way, $\Theta(2^n)$ bits randomized one-way, verifiable with $O(n^2)$ queries
-- statement:
--   Let $\mathrm{APFF}_n$ be Affine Pelagic Fourier Fishing (Problem 5.1): Alice holds $f:\{0,1\}^n\to\{-1,1\}$, Bob holds an $\ell$-dimensional subspace $V\le\mathbb F_2^n$ with $\ell=\lceil2\log_2n\rceil$, read through a fixed basis $b_1(V),\dots,b_\ell(V)$, and Bob must output $(a,y)\in\{0,1\}^n\times\{0,1\}^\ell$ satisfying the Pelagic condition (14) on the coset $U=V+a$. Then, for every choice of the basis $b(V)$:
--
--   1. For every $n\ge4$ there is an $n$-qubit quantum one-way protocol that succeeds with probability at least $3/4$ on every input $(f,V)$.
--   2. There are $c>0$ and $n_0$ such that for every $n\ge n_0$, every randomized public-coin one-way protocol with $m$-bit messages whose average success probability is at least $2/3$ when $f$ and $V$ are independent and uniform satisfies
--   $$
--   m\ge c\,2^n .
--   $$
--   3. $Q^1(\mathrm{APFF}_n)\le n$ for every $n\ge4$.
--   4. $R^1(\mathrm{APFF}_n)=\Theta(2^n)$: there are $c,C>0$ and $n_0$ with $c\,2^n\le R^1(\mathrm{APFF}_n)\le C\,2^n$ for all $n\ge n_0$.
--   5. Answers are efficiently verifiable: there are a step map $\delta$ computable in polynomial time by a Turing machine and a constant $C$ such that, for every $n\ge4$, every $V$, every candidate $(a,y)$ and every $f$, the deterministic query algorithm with step map $\delta$, given the basis $b(V)$, $a$ and $y$ and query access to $f$, halts after at most $Cn^2$ queries and accepts exactly when $(a,y)$ is a correct answer.
--
--   The constants in 2, 4 and 5 are chosen before $n$, the basis choice and the protocol. The theorem gives an optimal $n$ versus $\Theta(2^n)$ quantum–classical separation in one-way communication for a problem whose answers can be checked with $O(n^2)$ queries.
--
--   **Formalization Note** $Q^1$ and $R^1$ are at error $1/3$ (worst case over inputs). The running time of the verifier is polynomial in $n$ because each of its at most $Cn^2+1$ steps runs a polynomial-time machine on a word of length $O(n^2)$.
--
--   Differences from the source:
--   - encoding: f : {0,1}ⁿ → {−1,1} → Bool-valued f read through OAI.Cotype.sign (false ↦ 1, true ↦ −1); reason: a bijection of value sets; same instances
--   - encoding: ℓ = ⌈2 log₂ n⌉ → Nat.clog 2 (n²); reason: the same number for n ≥ 1
--   - generalization: one publicly fixed canonical basis b₁(V), …, b_ℓ(V), not named in the paper → every basis choice bas (a basis of every ℓ-dimensional subspace), with all constants chosen before bas; reason: specializes to the paper's basis whichever it is
--   - reading: the verifier is given a basis of V → the verifier is given the basis bas V through which y is read; reason: the validity of (a, y) depends on the basis that identifies y with an element of V*, so the verifier must be given that basis; the paper does not say how its canonical basis is computed
--   - encoding: a deterministic algorithm with query access to f using O(n²) queries and poly(n) time → a step map δ : List Bool → List Bool with Nonempty (Turing.TM2ComputableInPolyTime id id δ), run by queryRun on the input word (n in unary, a, y, the basis bits) for at most C n² + 1 steps, i.e. at most C n² queries; reason: a standard oracle-machine model: each step is polynomial in the configuration length O(n²), so the total time is poly(n)
--   - encoding: quantum one-way protocol with m qubits, shared randomness, no entanglement → published PelagicFF.OneWayQProtocol: finite coin law, density operator on Fin m → Bool per (coin, Alice input), POVM per (coin, Bob input); reason: the model of §2.1, p.14; same protocols
--   - encoding: randomized public-coin one-way protocol communicating c bits → OneWayProtocol: finite coin law, Alice's c-bit message Fin c → Bool per (coin, input), Bob's output per (coin, message, input); reason: the model of §2.1, p.14 and pp.45, 60 (a c-bit message takes at most 2^c values); private coins are subsumed by public coins
--   - encoding: Alice's and Bob's inputs independent and uniform → the uniform law on the product of the input sets (avgSucc); reason: independent uniform marginals are the uniform product law
--   - encoding: Ω(2ⁿ), Θ(2ⁿ), O(n²) for all sufficiently large n → ∃ constants and a threshold n₀, chosen before n and the protocol; reason: standard meaning of the asymptotic notation
--   - encoding: Q¹ and R¹ at ε = 1/3 (minimum costs of protocols succeeding with probability ≥ 2/3 on every input) → sInf over ℕ (published PelagicFF.Q1 and R1); reason: the sets are nonempty for APFFₙ, so sInf is the minimum
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem 5.2 (restatement of Theorem 1.2), p.32; Theorem 1.2, p.4

import Mathlib
import Definitions.Def_PelagicFF_PFF
import Definitions.Def_PelagicFF_OneWayQProtocol
import Definitions.Def_PelagicFF_Q1
import Definitions.Def_PelagicFF_Supplement_OneWayProtocol
import Definitions.Def_PelagicFF_Supplement_R1
import Definitions.Def_PelagicFF_Supplement_APFF
import Definitions.Def_PelagicFF_Supplement_queryRun

namespace PelagicFF.Supplement

/-- **Theorem 5.2 (Restatement of Theorem 1.2).** Anselm, Ding, Gilboa, Grewal, *Optimal and
Verifiable Quantum Advantages in Communication Complexity*, arXiv:2610.05585 (held version, sha256
4564aef3…), Theorem 5.2, p.32 (= Theorem 1.2, p.4):

"For all n ≥ 4, APFFₙ admits an n-qubit quantum one-way communication protocol that succeeds with
probability at least 3/4 on every input. Meanwhile, for all sufficiently large n, every randomized
public-coin one-way communication protocol for APFFₙ with success probability at least 2/3 on
average when Alice's truth table and Bob's subspace are sampled independently and uniformly at
random communicates Ω(2ⁿ) bits. In particular, Q¹(APFFₙ) ≤ n and R¹(APFFₙ) = Θ(2ⁿ). Furthermore,
answers to APFFₙ are efficiently verifiable. Specifically, there exists a deterministic algorithm
that, given a basis of V, a candidate answer (a, y), and query access to f, decides whether (a, y)
is a valid answer using O(n²) queries to f and poly(n) time."

The five clauses, in order: (a) the `n`-qubit protocol, success `≥ 3/4` on every input, for every
`n ≥ 4`; (b) `Ω(2ⁿ)` against every public-coin one-way protocol with average success `≥ 2/3` under
the uniform law on `(f, V)`; (c) `Q¹(APFFₙ) ≤ n`; (d) `R¹(APFFₙ) = Θ(2ⁿ)`, both bounds; (e) the
verifier: one step map `δ`, polynomial-time on a Turing machine, such that for every `n ≥ 4` the
query algorithm run with `δ` halts after at most `C n²` queries and accepts exactly the valid
answers.

**Formalization Note.** Every clause holds for every choice `bas` of the "publicly fixed canonical
basis" (which the paper does not name), with the constants fixed before `bas`. The verifier is
given the basis `bas V` in which `y` is read. -/
theorem theorem_5_2 :
    (∀ n ≥ 4, ∀ bas : BasisChoice n,
      ∃ P : PelagicFF.OneWayQProtocol (PelagicFF.BoolFn n) (Grass n (ell n)) (APFFOut n) n,
        ∀ f V, (3 : ℝ) / 4 ≤ P.succProb (APFF bas) f V) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ bas : BasisChoice n, ∀ m : ℕ,
      ∀ P : OneWayProtocol (PelagicFF.BoolFn n) (Grass n (ell n)) (APFFOut n) m,
        (2 : ℝ) / 3 ≤ P.avgSucc (APFF bas) → c * 2 ^ n ≤ (m : ℝ)) ∧
    (∀ n ≥ 4, ∀ bas : BasisChoice n, PelagicFF.Q1 (APFF bas) ≤ n) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ bas : BasisChoice n,
      c * 2 ^ n ≤ (R1 (APFF bas) : ℝ) ∧ (R1 (APFF bas) : ℝ) ≤ C * 2 ^ n) ∧
    (∃ δ : List Bool → List Bool, Nonempty (Turing.TM2ComputableInPolyTime id id δ) ∧
      ∃ C : ℕ, ∀ n ≥ 4, ∀ (bas : BasisChoice n) (V : Grass n (ell n)) (a : Fin n → ZMod 2)
        (y : Fin (ell n) → Bool) (f : PelagicFF.BoolFn n),
        ∃ b : Bool, queryRun δ n f (C * n ^ 2 + 1)
            (inputWord n (fun i => ((bas V i : V.1) : Fin n → ZMod 2)) a y) = some b ∧
          (b = true ↔ APFF bas f V (a, y))) := by sorry

end PelagicFF.Supplement
