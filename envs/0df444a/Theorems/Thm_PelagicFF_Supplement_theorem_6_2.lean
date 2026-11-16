-- Prove2me | Theorems.Thm_PelagicFF_Supplement_theorem_6_2
-- name    : PelagicFF.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:30:18.614425+00:00
-- url     : https://prove2.me/theorems/03b80747-8222-49a1-a8a0-74c74431c69d
-- title:
--   Theorem 6.2 — $\mathrm{DDP}_{n,d}$: exact level-$d$ protocol with a Clifford measurement, $\Theta_d(n^d)$ classical bits, $\Theta(n^d/\log n)$ gates
-- statement:
--   Let $\mathrm{DDP}_{n,d}$ be the Directional Derivative Problem (Problem 6.1): Alice holds $q\in V_{n,d}$ (zero-constant-term polynomials over $\mathbb F_2$ of degree at most $d$), Bob holds $a\in\mathbb F_2^n\setminus\{0\}$, and Bob must output $(x,b)$ with $b=q(x+a)+q(x)$. For every $d\ge2$:
--
--   1. There are a finite set $\Gamma_d$ of one- and two-qubit unitary gates and constants $C_d$, $n_0$ such that for every $n\ge d$ there is a quantum one-way protocol with $n$-qubit messages that
--      - succeeds with probability $1$ on every input,
--      - sends only level-$d$ messages $U|0^n\rangle$, $U\in C_d(n)$,
--      - uses only Clifford measurements (a Clifford unitary, a computational-basis measurement, a relabelling of the outcome), and,
--      - when $n\ge n_0$, sends only messages that can be prepared from $|0^n\rangle$, up to global phase, by at most $C_d\,n^d/\log n$ gates of $\Gamma_d$.
--   2. There are $c_d>0$ and $n_0$ such that for every $n\ge n_0$ every randomized one-way protocol with $m$-bit messages and average success probability at least $2/3$ under uniform and independent $q$ and $a$ satisfies $m\ge c_d\,n^d$.
--   3. There are $C_d$ and $n_0$ such that for every $n\ge n_0$ there is an exact (deterministic) classical one-way protocol with at most $C_d\,n^d$ bits.
--   4. The gate bound is optimal up to a factor depending on $d$: for every finite set $\Gamma$ of one- and two-qubit unitary gates there are $c>0$ and $n_0$ such that for every $n\ge n_0$, every $n$-qubit quantum one-way protocol with average success probability at least $2/3$ under uniform inputs, all of whose messages can be prepared by at most $G$ gates of $\Gamma$, satisfies
--   $$
--   G\ge c\,\frac{n^d}{\log n}.
--   $$
--
--   So $\mathrm{DDP}_{n,d}$ separates $n$ qubits from $\Theta_d(n^d)$ classical bits with quantum messages of optimal gate complexity.
--
--   **Formalization Note** Bob's measurement is unrestricted in 4. The logarithm is natural; another base changes only the constants.
--
--   Differences from the source:
--   - encoding: V_{n,d}, zero-constant-term multilinear polynomials of degree ≤ d → coefficient vectors (q_S) over the monomials with 1 ≤ |S| ≤ d; reason: distinct coefficient vectors are distinct polynomials; same uniform law
--   - encoding: C_d(n) with C₁ = {e^{iθ}P} → published TeleportGates.Ck.cliffordLevel n (d − 1), whose C₁ has phases ±1, ±i; reason: the hierarchies coincide at every level ≥ 2, and d ≥ 2
--   - encoding: a Clifford measurement → IsCliffordMeasurement: a C₂(n) unitary U, a computational-basis measurement and a relabelling g; POVM element ∑_{s : g(s) = z} U†|s⟩⟨s|U; reason: the measurement of Lemma 6.3, pp.43–44
--   - reading: Alice's message can be prepared using Oᵈ(nᵈ/log n) one- and two-qubit gates (printed with a superscript d) → the messages of the exact protocol of clause 1 are each prepared exactly (as density matrices, so up to global phase) by at most C_d nᵈ/log n gates of a finite one- and two-qubit gate set Γ_d depending only on d, by a circuit on the n message wires (no ancillas), for n ≥ n₀; reason: Corollary 6.14, p.54 fixes the gate set depending only on d and preparation up to global phase; the printed Oᵈ is O_d, as in Theorem 1.3, p.5 and Corollary 6.14, p.54
--   - reading: this upper bound is asymptotically optimal up to a factor depending on d → for every finite one- and two-qubit gate set Γ there are c > 0 and n₀ such that every n-qubit protocol with average success ≥ 2/3 under uniform inputs whose every message is prepared by ≤ G gates of Γ (a circuit on the n message wires, no ancillas) has G ≥ c nᵈ / log n; reason: the argument and statement of §6.4, p.54 ("every n-qubit message can be prepared by a circuit of at most G gates"): with G gates Alice can send a circuit description of O(G log n) bits
--   - encoding: an exact classical one-way protocol → an exact deterministic one-way protocol; reason: equivalent: in an exact public-coin protocol with finitely many coins every coin value of positive probability gives an exact deterministic protocol
--   - encoding: quantum one-way protocol with m qubits, shared randomness, no entanglement → published PelagicFF.OneWayQProtocol: finite coin law, density operator on Fin m → Bool per (coin, Alice input), POVM per (coin, Bob input); reason: the model of §2.1, p.14; same protocols
--   - encoding: randomized public-coin one-way protocol communicating c bits → OneWayProtocol: finite coin law, Alice's c-bit message Fin c → Bool per (coin, input), Bob's output per (coin, message, input); reason: the model of §2.1, p.14 and pp.45, 60 (a c-bit message takes at most 2^c values); private coins are subsumed by public coins
--   - encoding: Alice's and Bob's inputs independent and uniform → the uniform law on the product of the input sets (avgSucc); reason: independent uniform marginals are the uniform product law
--   - encoding: Ω_d, O_d → for every d ≥ 2, ∃ constants and a threshold n₀ depending on d (and in clause 4 on Γ), chosen before n and the protocol; reason: standard meaning of the subscripted asymptotic notation
--   - encoding: log n → Real.log n (natural logarithm); reason: a change of base changes only the constants
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem 6.2 (restatement of Theorem 1.3), pp.42–43; Theorem 1.3, p.5; Lemma 6.3, p.43; Lemma 6.10, p.52; Corollary 6.12, p.53; §6.4 and Corollary 6.14, p.54

import Mathlib
import Definitions.Def_PelagicFF_OneWayQProtocol
import Definitions.Def_PelagicFF_Supplement_OneWayProtocol
import Definitions.Def_PelagicFF_Supplement_DetOneWayProtocol
import Definitions.Def_PelagicFF_Supplement_qAvgSucc
import Definitions.Def_PelagicFF_Supplement_DDP
import Definitions.Def_PelagicFF_Supplement_LevelMessage
import Definitions.Def_PelagicFF_Supplement_PreparedWithin

namespace PelagicFF.Supplement

/-- **Theorem 6.2 (Restatement of Theorem 1.3).** Anselm, Ding, Gilboa, Grewal, *Optimal and
Verifiable Quantum Advantages in Communication Complexity*, arXiv:2610.05585 (held version, sha256
4564aef3…), Theorem 6.2, pp.42–43 (= Theorem 1.3, p.5):

"For every d ≥ 2 and n ≥ d, there is an exact quantum one-way communication protocol for DDP_{n,d}
using an n-qubit level-d message and a Clifford measurement. By contrast, under the uniform input
distribution, every randomized classical one-way protocol for DDP_{n,d} with average success
probability at least 2/3 uses Ω_d(nᵈ) bits of communication. There is also an exact classical
one-way protocol with O_d(nᵈ) bits of communication. Moreover, Alice's message can be prepared
using O_d(nᵈ/log n) one- and two-qubit gates, and this upper bound is asymptotically optimal up to
a factor depending on d."

The four clauses, in order, each for every `d ≥ 2`: (a) a finite gate set `Γ_d` of one- and
two-qubit gates and constants `C_d, n₀` such that for every `n ≥ d` there is an exact `n`-qubit
protocol whose every message is a level-`d` message, whose every measurement is a Clifford
measurement, and (for `n ≥ n₀`) whose every message is prepared by at most `C_d nᵈ / log n` gates
of `Γ_d`; (b) `Ω_d(nᵈ)` against every randomized one-way protocol with average success `≥ 2/3`
under uniform `q ∈ V_{n,d}` and uniform `a ≠ 0`; (c) an exact deterministic one-way protocol with
`O_d(nᵈ)` bits; (d) optimality: for every finite gate set `Γ` of one- and two-qubit gates there
are `c > 0` and `n₀` such that, for `n ≥ n₀`, every `n`-qubit protocol with average success `≥ 2/3`
under the uniform law whose every message is prepared by at most `G` gates of `Γ` has
`G ≥ c nᵈ / log n`.

**Formalization Note.** "Exact" is success probability `1` on every input; an exact randomized
classical protocol has an exact coin fixing, so (c) is stated for deterministic protocols. The
logarithm is natural (a constant factor). Clause (d) follows the reading of §6.4, p.54: the gate
set is fixed, the constant may depend on it and on `d`, and Bob's measurement is unrestricted. -/
theorem theorem_6_2 :
    (∀ d ≥ 2, ∃ Γ : Set QAlgorithms.Gate, IsGateSet12 Γ ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n ≥ d,
      ∃ P : PelagicFF.OneWayQProtocol (Vnd n d) (Dir n) (DDPOut n) n,
        (∀ q a, P.succProb (DDP n d) q a = 1) ∧
        (∀ r q, IsLevelMessage d (P.state r q)) ∧
        (∀ r a, IsCliffordMeasurement (P.meas r a)) ∧
        (n₀ ≤ n → ∀ r q, PreparedWithin Γ (C * (n : ℝ) ^ d / Real.log n) (P.state r q))) ∧
    (∀ d ≥ 2, ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
      ∀ P : OneWayProtocol (Vnd n d) (Dir n) (DDPOut n) m,
        (2 : ℝ) / 3 ≤ P.avgSucc (DDP n d) → c * (n : ℝ) ^ d ≤ (m : ℝ)) ∧
    (∀ d ≥ 2, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ m : ℕ, (m : ℝ) ≤ C * (n : ℝ) ^ d ∧
      ∃ P : DetOneWayProtocol (Vnd n d) (Dir n) (DDPOut n) m, P.IsExact (DDP n d)) ∧
    (∀ d ≥ 2, ∀ Γ : Set QAlgorithms.Gate, IsGateSet12 Γ →
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : ℕ,
        ∀ P : PelagicFF.OneWayQProtocol (Vnd n d) (Dir n) (DDPOut n) n,
          (2 : ℝ) / 3 ≤ qAvgSucc P (DDP n d) →
          (∀ r q, PreparedWithin Γ (G : ℝ) (P.state r q)) →
          c * (n : ℝ) ^ d / Real.log n ≤ (G : ℝ)) := by sorry

end PelagicFF.Supplement
