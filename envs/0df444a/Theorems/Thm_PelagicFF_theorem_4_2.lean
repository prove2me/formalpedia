-- Prove2me | Theorems.Thm_PelagicFF_theorem_4_2
-- name    : PelagicFF.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:53.899203+00:00
-- url     : https://prove2.me/theorems/c902c31f-d97d-4893-a9a6-7116ddc97f88
-- title:
--   Theorem 4.2 — $\mathrm{PFF}_n$: $n$ qubits one-way, $\Theta(2^n)$ bits randomized two-way
-- statement:
--   This is the paper's main result: an optimal quantum–classical separation for a total search problem, holding even against two-way randomized communication.
--
--   Let $\mathrm{PFF}_n$ be Pelagic Fourier Fishing (Problem 4.1). Then:
--
--   1. For every $n\in\mathbb N$, $\mathrm{PFF}_n$ has an $n$-qubit quantum one-way protocol (shared randomness, no entanglement) that succeeds with probability at least $3/4$ on **every** input $(f,g)$.
--   2. There are $c>0$ and $n_0$ such that for every $n\ge n_0$, every randomized public-coin two-way protocol for $\mathrm{PFF}_n$ whose success probability, averaged over uniformly random $(f,g)$, is at least $2/3$ has cost
--   $$\mathrm{cost}\ \ge\ c\cdot 2^n .$$
--   3. For every $n$, $Q^1(\mathrm{PFF}_n)\le n$.
--   4. $R(\mathrm{PFF}_n)=\Theta(2^n)$: there are $c,C>0$ and $n_0$ with $c\cdot2^n\le R(\mathrm{PFF}_n)\le C\cdot2^n$ for all $n\ge n_0$.
--
--   Since any $n$-qubit one-way protocol can be simulated classically with $O(2^n)$ bits, the separation is the largest possible.
--
--   **Formalization Note** In a classical protocol Bob's output is his leaf function applied to his input; cost is the depth maximized over inputs and coin values of positive probability. $Q^1$ and $R$ are at error $1/3$.
--
--   Differences from the source:
--   - encoding: Boolean functions with values in {−1,1} → Bool-valued functions read through OAI.Cotype.sign (false ↦ 1, true ↦ −1); reason: a bijection of value sets; same instances
--   - encoding: quantum one-way protocol with shared randomness and no prior entanglement, n qubits → OneWayQProtocol: finite coin law; density operator on Fin n → Bool per (coin, Alice input); POVM per (coin, Bob input); reason: this is the model of §2.1, p.14; same protocols
--   - encoding: randomized public-coin two-way protocol communicating c bits → PubCoinProtocol: finite coin law and one deterministic tree per coin whose leaves are Bob's output functions; cost = maximum depth over coins of positive probability; reason: a public-coin protocol is a distribution over deterministic protocols (p.30) and its communication is the worst-case number of bits sent
--   - encoding: Ω(2ⁿ) and Θ(2ⁿ) for all sufficiently large n → ∃ c > 0 (and C > 0), ∃ n₀, ∀ n ≥ n₀, with the constants chosen before n and the protocol; reason: standard meaning of the asymptotic notation
--   - encoding: Q¹ and R at ε = 1/3 (minimum costs of protocols succeeding with probability ≥ 2/3 on every input) → sInf over ℕ of the qubit numbers / costs of such protocols (Q1, Rcc); reason: the sets are nonempty for PFFₙ, so sInf is the minimum
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem 4.2 (restatement of Theorem 1.1), p.27; Theorem 1.1, pp.3–4

import Mathlib
import Definitions.Def_PelagicFF_PFF
import Definitions.Def_PelagicFF_OneWayQProtocol
import Definitions.Def_PelagicFF_Q1
import Definitions.Def_PelagicFF_PubCoinProtocol
import Definitions.Def_PelagicFF_Rcc

namespace PelagicFF

/-- **Theorem 4.2 (Restatement of Theorem 1.1).** Anselm, Ding, Gilboa, Grewal, *Optimal and
Verifiable Quantum Advantages in Communication Complexity*, arXiv:2610.05585 (held version, sha256
4564aef3…), Theorem 4.2, p.27 (= Theorem 1.1, pp.3–4):

"For all n ∈ ℕ, PFFₙ admits an n-qubit quantum one-way communication protocol that succeeds with
probability at least 3/4 on every input. Meanwhile, for all sufficiently large n, every randomized
public-coin (two-way) communication protocol for PFFₙ with success probability at least 2/3 on
average under a uniform input distribution communicates Ω(2ⁿ) bits. In particular,
Q¹(PFFₙ) ≤ n and R(PFFₙ) = Θ(2ⁿ)."

The four clauses, in order: (a) an `n`-qubit one-way protocol with success `≥ 3/4` on every input,
for every `n`; (b) `Ω(2ⁿ)`: one constant `c > 0` and one threshold `n₀`, fixed before `n` and the
protocol, such that every public-coin two-way protocol with average success `≥ 2/3` under the uniform
law on `(f, g)` has cost `≥ c·2ⁿ`; (c) `Q¹(PFFₙ) ≤ n`; (d) `R(PFFₙ) = Θ(2ⁿ)`, both bounds.

**Formalization Note.** Bob's output in a classical protocol is the leaf function applied to his
input (§4.2.2, p.30); the cost is the depth maximized over inputs and coin values of positive
probability; quantum protocols have shared randomness and no entanglement (§2.1, p.14). -/
theorem theorem_4_2 :
    (∀ n : ℕ, ∃ P : OneWayQProtocol (BoolFn n) (BoolFn n) (Fin n → Bool) n,
        ∀ f g : BoolFn n, (3 : ℝ) / 4 ≤ P.succProb (PFF n) f g) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ P : PubCoinProtocol (BoolFn n) (BoolFn n) (Fin n → Bool),
          (2 : ℝ) / 3 ≤ P.avgSucc (PFF n) → c * 2 ^ n ≤ (P.cost : ℝ)) ∧
    (∀ n : ℕ, Q1 (PFF n) ≤ n) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        c * 2 ^ n ≤ (Rcc (PFF n) : ℝ) ∧ (Rcc (PFF n) : ℝ) ≤ C * 2 ^ n) := by sorry

end PelagicFF
