-- Prove2me | Theorems.Thm_QIndInf_Supplement_theorem_4_4
-- name    : QIndInf.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:28:54.576753+00:00
-- url     : https://prove2.me/theorems/f8ec0125-4d75-4009-8773-433a6aa7f5e7
-- title:
--   Theorem 4.4 — infinitely-often one-way puzzles make average-case universal quantum inductive inference hard
-- statement:
--   Fix a finite universal gate set. If infinitely-often one-way puzzles exist (Definition 3.7), then for every polynomial $r:\mathbb N^4\to\mathbb N$ there is no QPT algorithm $L$ that solves average-case universal quantum inductive inference (Definition 4.3) with round complexity $r$:
--   $$\exists\ \text{io-OWPuzz}\ \Longrightarrow\ \forall r\ \text{polynomial},\quad \neg\,\exists L\ \text{QPT}:\ L\ \text{solves average-case universal quantum inductive inference with round complexity } r .$$
--
--   Theorem 4.2 shows that the task is solvable information-theoretically with $O(s\epsilon^{-2}\delta^{-1})$ rounds; this theorem shows that no efficient learner achieves any polynomial number of rounds under a minimal quantum cryptographic assumption, even on average over efficiently sampled instances.
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
--   - encoding: instrument specified by a circuit description implementing it → circuit with n input wires and n + k output wires (first n = post-measurement register R_i, last k = outcome bits, measured); the instrument with 2^k outcomes it implements (instrOf); reason: a circuit description determines the instrument; a finite outcome set is padded to 2^k outcomes with zero branches
--   - encoding: L outputs a state on (R1, …, Ri, Xi) → a round counts as a success only if L writes a circuit with i·n − n input and i·n + K output wires (OutputsOn), whose channel is compared with the base target; reason: excludes only ill-formed outputs, which are not states on (R1, …, Ri, Xi)
--   - encoding: polynomial r : ℕ⁴ → ℕ → MvPolynomial (Fin 4) ℕ evaluated at (λ, s, p, q); reason: polynomials with natural coefficients; every polynomial bound is dominated by one
--   - encoding: TD(ρ, σ) = ½‖ρ − σ‖₁ → ½ · WildeQIT.traceDist; reason: the published traceDist is the unnormalized trace norm
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), §4.3, Theorem 4.4, p.22 (= Theorem 1.3, p.7), proof pp.22–23; Definition 3.7, p.17; Definition 4.3, pp.21–22

import Mathlib
import Definitions.Def_QIndInf_Supplement_IsIoOWPuzz
import Definitions.Def_QIndInf_Supplement_SolvesAvg

set_option autoImplicit false

namespace QIndInf.Supplement

open QiOPoQ

/-- **Theorem 4.4 (average-case hardness of universal quantum inductive inference).** Over any
finite universal gate set: if infinitely-often one-way puzzles exist, then for every polynomial
`r : ℕ⁴ → ℕ` there is no QPT algorithm that solves average-case universal quantum inductive
inference (Definition 4.3) with round complexity `r`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.3, Theorem 4.4, p.22 (= Theorem 1.3, p.7); Definition 3.7,
p.17; Definition 4.3, pp.21–22.

**Formalization Note.**
* The paper fixes an arbitrary finite universal gate set; the statement holds for each one
  (`IsUniversalGateSet G`). Every algorithm (sampler, adversary, learner, instance generator), every
  instrument and every source circuit is over the same `G`; Turing machines are the published
  Complexitylib multi-tape machines with binary descriptions (`tmRun`).
* `r` ranges over polynomials with natural coefficients in `(λ, s, p, q)`. -/
theorem theorem_4_4 (G : GateSet) (hG : IsUniversalGateSet G) (hOW : IoOWPuzzExists G) :
    ∀ r : MvPolynomial (Fin 4) ℕ,
      ¬ ∃ L : List Bool, IsQPT L ∧
        SolvesAvg G L (fun lam s p q => MvPolynomial.eval ![lam, s, p, q] r) := by sorry

end QIndInf.Supplement
