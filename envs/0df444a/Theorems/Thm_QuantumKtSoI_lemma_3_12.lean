-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_3_12
-- name    : QuantumKtSoI.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:13.89519+00:00
-- url     : https://prove2.me/theorems/c3339f30-5f71-4a88-ab42-ed76c8099032
-- title:
--   Lemma 3.12 — universal machine
-- statement:
--   Fix admissible glue routines. There are a machine $U$ and a polynomial $q_U$ with nonnegative integer coefficients such that for all strings $e,x$ and every integer $t\ge1$, on input $\langle e,\langle x,\mathrm b(t)\rangle\rangle$ the machine $U$ halts within $q_U(|e|+|x|+t)$ steps, its output is either $0$ or $1w$ for a string $w$, and
--   $$P_U\big(\langle e,\langle x,\mathrm b(t)\rangle\rangle;\,q_U(|e|+|x|+t),\,1w\big)=\begin{cases}P_e(x;t,w)& e\in E,\\ 0&\text{otherwise.}\end{cases}$$
--
--   The universal machine lets later algorithms enumerate descriptions and sample their outputs up to a deadline.
--
--   Differences from the source:
--   - generalization: the paper's glue routines, fixed once and for all and described only by their properties (p.24) → every admissible glue-routine set G (GlueRoutines.Admissible: local rules of Definition 3.1, exit within c₀(|x|+|u|+|v|+ℓ+1) steps with the glue map written and all heads on cell 0); reason: the proofs use only the p.24 properties, so the paper's routine set is one admissible instance
--   - reading: AMP loading, comparison and copy routines described only by their behaviour (pp.25–26, p.29) → routines pinned step by step in ampCore (loading sweep of 2|x|+3 steps; the two comparison heads return together; the copy routine returns copy i's output head, then copies in one sweep); reason: the paper leaves these routines unspecified beyond the stated behaviour; this is the most direct implementation of it
--   - reading: a standard injective binary encoding ⌜A⌝ of machines (p.23) → the fixed encoding CodedMachine.encode, every field written as a self-delimiting number in a fixed order; reason: the paper fixes the encoding only by its contents; by Corollary 9.5 (p.119) admissible encodings change qKt by O(log)
--   - encoding: P_M(x;t,w) = Σ ‖ψ_ρ‖² over ρ ∈ Rᵗ with ψ_ρ ≠ 0, st(ρ) final, out(ρ) = w (Definition 3.4) → Σ_{ρ ∈ recSeqs} Σ_{C final, output C = w} |ψ_ρ(C)|²; reason: equal by Lemma 3.3(iii): the support of a nonzero branch vector shares state and output; sequences outside recSeqs have ψ_ρ = 0
--   - encoding: descriptions e ∈ E charged |e| (Definition 3.6) → e : Desc charged |Desc.bits e|; reason: by Lemma 3.7 each string of E has exactly one parse, so ranging over Desc is ranging over E
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
--   - encoding: a (fixed) machine of Definition 3.1 used as a component or decider → a valid coded machine (CodedMachine.Valid); reason: every machine of Definition 3.1 has such a code up to renaming of states, tapes and symbols; the paper uses these machines as BASE(·) leaves
--   - encoding: its output is either 0 or 1w → every output other than [false] and true :: w has probability 0 at the deadline; reason: U halts within the deadline on every branch, so the outputs of its branches are exactly the outputs of positive probability
--   - encoding: e ∈ E → e = bits d for some description d; reason: E is the set of description strings; the parse is unique (Lemma 3.7)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 3.12, p.31

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 3.12** (Universal machine; Myrisiotis, STOC 2027 submission, held version sha256
6616571c…, p.31). There is a machine `U` and a polynomial `q_U` with nonnegative integer
coefficients, hence nondecreasing, with the following property. For all strings `e` and `x` and
every integer `t ≥ 1`, on input `⟨e,⟨x,b(t)⟩⟩` the machine `U` halts within `q_U(|e|+|x|+t)` steps,
its output is either `0` or `1w` for a string `w`, and
`P_U(⟨e,⟨x,b(t)⟩⟩; q_U(|e|+|x|+t), 1w) = P_e(x;t,w)` if `e ∈ E`, and `0` otherwise.

**Formalization Note** `U` is a valid coded machine. "`e ∈ E`" is "`e = bits d` for a description
`d`" (unique by Lemma 3.7); "its output is either `0` or `1w`" says that every other output has
probability `0` at that deadline. -/
theorem lemma_3_12 (G : GlueRoutines) (hG : G.Admissible) :
    ∃ U : CodedMachine, U.Valid ∧ ∃ qU : Polynomial ℕ,
      ∀ (e x : List Bool) (t : ℕ), 1 ≤ t →
        U.toMachine.HaltsWithin (pair e (pair x (bin t))) (qU.eval (e.length + x.length + t)) ∧
          (∀ w' : List Bool,
            0 < U.toMachine.outputProb (pair e (pair x (bin t)))
                (qU.eval (e.length + x.length + t)) w' →
              w' = [false] ∨ ∃ w, w' = true :: w) ∧
          ∀ w : List Bool,
            (∀ d : Desc, d.bits = e →
              U.toMachine.outputProb (pair e (pair x (bin t)))
                (qU.eval (e.length + x.length + t)) (true :: w) = d.prob G x t w) ∧
            ((∀ d : Desc, d.bits ≠ e) →
              U.toMachine.outputProb (pair e (pair x (bin t)))
                (qU.eval (e.length + x.length + t)) (true :: w) = 0) := by sorry

end QuantumKtSoI
