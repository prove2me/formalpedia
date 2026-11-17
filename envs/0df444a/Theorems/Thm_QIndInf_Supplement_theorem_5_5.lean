-- Prove2me | Theorems.Thm_QIndInf_Supplement_theorem_5_5
-- name    : QIndInf.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:30:50.091634+00:00
-- url     : https://prove2.me/theorems/be66fcaf-9e93-4445-aeec-53e7896bb837
-- title:
--   Theorem 5.5 — infinitely-often one-way puzzles exist iff POVM-based inference is hard on average
-- statement:
--   Fix a finite universal gate set and let $g:\mathbb N\to\mathbb N$ be superconstant ($g(\lambda)\to\infty$) and polynomially bounded. Say that $L$ solves average-case POVM-based universal quantum inductive inference (Definition 5.4) with round complexity $O\big((s(\lambda)+g(\lambda))p(\lambda)^2q(\lambda)\big)$ if it does so with round complexity $C\,(s+g(\lambda))\,p^2q$ for some constant $C$. Then:
--
--   1. if infinitely-often one-way puzzles exist, no QPT algorithm solves average-case POVM-based universal quantum inductive inference with round complexity $O\big((s+g)p^2q\big)$;
--   2. if infinitely-often one-way puzzles do not exist, some QPT algorithm solves it with round complexity $O\big((s+g)p^2q\big)$.
--
--   Together:
--   $$\exists\ \text{io-OWPuzz}\iff\neg\,\exists L\ \text{QPT solving average-case POVM-based inference with round complexity } O\big((s+g)p^2q\big).$$
--
--   This characterizes the average-case hardness of predicting measurement outcomes of efficiently generated quantum sources by the existence of the weakest standard quantum cryptographic primitive.
--
--   Differences from the source:
--   - reading: fix an arbitrary finite universal quantum gate set G → every QiOPoQ.GateSet G (contains I, X, CNOT, closed under adjoints) with IsUniversalGateSet G (dense, gate entries computable in polynomial time); reason: the paper fixes an arbitrary such set; the statement is made for each admissible choice, and QPT is the same class for every finite universal gate set
--   - encoding: classical Turing machine T with binary description, |T|, T^t → Complexitylib multi-tape machine decoded from the bit string T (decodeDesc), run for t steps by the published universal function; |T| = T.length; reason: the paper fixes no machine model; every multi-tape machine has a description
--   - encoding: QPT algorithm (sampler, adversary, learner) → description of a classical machine halting within P(|x|) steps that writes a circuit over G with the input hard-wired; classical output = measured output register, quantum input/output = the circuit's channel; reason: the standard uniform polynomial-size circuit model, without advice
--   - reading: t′(λ)-time algorithm G → quantum algorithm whose classical generator halts within t′(λ) steps on 1^λ; its output is a measured circuit, so G may be randomized; reason: the proof of Theorem 4.4 calls G a QPT algorithm and the proof of Theorem 5.5 runs G from its description for t′(λ) steps (p.26)
--   - encoding: polynomials m, n, s, t, t′, p, q → Polynomial ℕ with m(λ), p(λ), q(λ) ≥ 1 for all sufficiently large λ; reason: i ← [m], ε = 1/p(λ) and δ = 1/q(λ) need positive values where the success condition is asked (large λ); this excludes only the zero polynomials
--   - encoding: G outputs T with |T| ≤ s(λ) whose run writes a circuit description, and m(λ) instruments/POVMs on the registers → required of every output of G of positive probability (ValidInstance / ValidPOVMInstance); reason: the paper states it as the syntax of G
--   - encoding: a circuit description of ρ^T, padded or traced to mn qubits (Eq. (40)) → srcFamily: the circuit written by T^t run on |0…0⟩, adjusted to jn qubits for every j; |0^{jn}⟩ if T^t writes no valid circuit; reason: Eq. (40) and the convention after it; register R_i is the i-th block of n qubits
--   - encoding: Samp outputs a pair (puzz, ans); A runs on (1^λ, puzz) → outputs that are not a tup-pair count as rejected; A runs on QiOPoQ.pair (unary λ) puzz; reason: Samp's syntax requires pairs; one fixed injective pairing
--   - reading: iff … with round complexity O((s(λ)+g(λ))p(λ)²q(λ)) for any superconstant g(λ) = ω(1) → two implications, each for every g with Tendsto g atTop atTop and g ≤ P for a polynomial P; O(f) = ∃ C, round complexity C·(s + g(λ))·p²·q; reason: the strength the proof gives (Eq. (112): m ≥ 8(s+1+|Ĝ|)p²q, and g(λ) ≥ |Ĝ|+1 eventually); for g above every polynomial no polynomial m ≥ C(s+g)p²q exists, Definition 5.4 is vacuous and implication 1 would be false
--   - reading: Definition 5.4: r : ℕ⁴ → ℕ a polynomial → r(λ, s, p, q) = C·(s + g(λ))·p²·q, an arbitrary function; reason: the theorem's own round complexity O((s+g)p²q) is not a polynomial for a general g
--   - encoding: POVM described as a quantum circuit implementing it → circuit with n input wires and k output wires, all measured; the POVM enters through the instrument E_x(ρ) = Tr[E_x ρ]|0^n⟩⟨0^n| (povmOf), so D^{M,ρ}_{<i} is the base outcomeProb; reason: p.25 identifies the POVM-based task with these instruments; finite outcome sets padded to 2^k
--   - encoding: SD(L(param, h<i, M_i), D^{M,ρ}_i(·|x<i)) → ½ ∑_w |Pr[L(…) = w] − Q(w)| over all strings w, Q carried by the outcome bit strings of M_i, D_i(y|x<i) = D_{≤i}(x<i, y)/D_{<i}(x<i); reason: the statistical distance of the two output distributions
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), §5.2, Theorem 5.5, p.25 (= Theorem 1.4, p.7), proof pp.25–28 (Eq. (112)); Definition 3.7, p.17; Definition 5.4, p.25

import Mathlib
import Definitions.Def_QIndInf_Supplement_IsIoOWPuzz
import Definitions.Def_QIndInf_Supplement_SolvesAvgPOVM

set_option autoImplicit false

namespace QIndInf.Supplement

open QiOPoQ

/-- **Theorem 5.5 (one-way puzzles ⇔ average-case hardness of POVM-based inference).** Over any
finite universal gate set, for every superconstant, polynomially bounded `g : ℕ → ℕ`:
1. if infinitely-often one-way puzzles exist, no QPT algorithm solves average-case POVM-based
   universal quantum inductive inference (Definition 5.4) with round complexity
   `O((s(λ) + g(λ)) p(λ)² q(λ))`;
2. if they do not exist, some QPT algorithm solves it with round complexity
   `O((s(λ) + g(λ)) p(λ)² q(λ))`.
"With round complexity `O(f)`" is "with round complexity `C·f` for some constant `C`".

arXiv:2609.36912 (PDF of 2026-11-02), §5.2, Theorem 5.5, p.25 (= Theorem 1.4, p.7), proof
pp.25–28 (the "if" direction gives `m ≥ 8(s(λ) + 1 + |Ĝ|)p(λ)²q(λ)`, Eq. (112)); Definition 3.7,
p.17; Definition 5.4, p.25.

**Formalization Note.**
* The two directions are stated separately, each for every admissible `g`, which is the strength
  the proof gives; together they give the printed "if and only if … for any superconstant `g`".
* `g` superconstant is `Tendsto g atTop atTop`. `g` is also polynomially bounded: for a `g` above
  every polynomial no polynomial `m` satisfies `m ≥ C(s + g)p²q`, Definition 5.4 holds vacuously,
  and direction 1 would fail; every function the paper's `O(·)` is meant for is polynomially
  bounded.
* The gate set, machines and algorithms are as in Theorem 4.4. -/
theorem theorem_5_5 (G : GateSet) (hG : IsUniversalGateSet G) :
    (IoOWPuzzExists G →
      ∀ g : ℕ → ℕ, Filter.Tendsto g Filter.atTop Filter.atTop →
        (∃ P : Polynomial ℕ, ∀ lam, g lam ≤ P.eval lam) →
        ¬ ∃ L : List Bool, IsQPT L ∧ ∃ C : ℕ,
          SolvesAvgPOVM G L (fun lam s p q => C * (s + g lam) * p ^ 2 * q)) ∧
    (¬ IoOWPuzzExists G →
      ∀ g : ℕ → ℕ, Filter.Tendsto g Filter.atTop Filter.atTop →
        (∃ P : Polynomial ℕ, ∀ lam, g lam ≤ P.eval lam) →
        ∃ L : List Bool, IsQPT L ∧ ∃ C : ℕ,
          SolvesAvgPOVM G L (fun lam s p q => C * (s + g lam) * p ^ 2 * q)) := by sorry

end QIndInf.Supplement
