-- Prove2me | Theorems.Thm_QuantumKtSoI_theorem_6_18
-- name    : QuantumKtSoI.theorem_6_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:42:02.331332+00:00
-- url     : https://prove2.me/theorems/7b33f15b-5e89-4094-8a0e-d4f0225e6793
-- title:
--   Theorem 6.18 — defect at the boundary exponent
-- statement:
--   Fix admissible glue routines. Fix a rational $a\ge1$ and a real $A\ge1$, and let $L$ be a language that is PSPACE-hard under deterministic polynomial-time many-one reductions. Suppose a machine of Definition 3.1 decides $L$, with error at most $1/3$, on every sufficiently large input length $M$, within $2^{A(\log(M+2))^a}$ steps on every branch. Then there is a rational $\eta>0$ such that infinitely many pairs $(u,v)$ satisfy
--   $$\Delta(u,v)\ >\ \eta\,(|u|+|v|)^{1/a}.$$
--
--   A fast quantum algorithm for a PSPACE-complete language forces symmetry of information to fail with a positive coefficient at the boundary exponent; for $a=1$ (a polynomial-time decider) the defect is linear.
--
--   Differences from the source:
--   - generalization: the paper's glue routines, fixed once and for all and described only by their properties (p.24) → every admissible glue-routine set G (GlueRoutines.Admissible: local rules of Definition 3.1, exit within c₀(|x|+|u|+|v|+ℓ+1) steps with the glue map written and all heads on cell 0); reason: the proofs use only the p.24 properties, so the paper's routine set is one admissible instance
--   - reading: AMP loading, comparison and copy routines described only by their behaviour (pp.25–26, p.29) → routines pinned step by step in ampCore (loading sweep of 2|x|+3 steps; the two comparison heads return together; the copy routine returns copy i's output head, then copies in one sweep); reason: the paper leaves these routines unspecified beyond the stated behaviour; this is the most direct implementation of it
--   - reading: a standard injective binary encoding ⌜A⌝ of machines (p.23) → the fixed encoding CodedMachine.encode, every field written as a self-delimiting number in a fixed order; reason: the paper fixes the encoding only by its contents; by Corollary 9.5 (p.119) admissible encodings change qKt by O(log)
--   - encoding: P_M(x;t,w) = Σ ‖ψ_ρ‖² over ρ ∈ Rᵗ with ψ_ρ ≠ 0, st(ρ) final, out(ρ) = w (Definition 3.4) → Σ_{ρ ∈ recSeqs} Σ_{C final, output C = w} |ψ_ρ(C)|²; reason: equal by Lemma 3.3(iii): the support of a nonzero branch vector shares state and output; sequences outside recSeqs have ψ_ρ = 0
--   - encoding: descriptions e ∈ E charged |e| (Definition 3.6) → e : Desc charged |Desc.bits e|; reason: by Lemma 3.7 each string of E has exactly one parse, so ranging over Desc is ranging over E
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
--   - encoding: qKt as a minimum of |e| + ⌈log t⌉ (Definition 4.1) → ℕ-valued sInf of the feasible costs, ⌈log t⌉ = Nat.clog 2 t; reason: the feasible set is nonempty (LIT(y), p.41), so the sInf is the minimum; Nat.clog 2 t = ⌈log₂ t⌉ for t ≥ 1
--   - encoding: a (fixed) machine of Definition 3.1 used as a component or decider → a valid coded machine (CodedMachine.Valid); reason: every machine of Definition 3.1 has such a code up to renaming of states, tapes and symbols; the paper uses these machines as BASE(·) leaves
--   - generalization: the PSPACE-complete language L⋆ of Theorem 2.4 → every language L that is PSPACE-hard under deterministic polynomial-time many-one reductions (PSPACEHard); reason: the proof uses only the reduction of a PSPACE language to L⋆ (p.90); L⋆ is such a language by Theorem 2.4
--   - reading: PSPACE decided by a deterministic multi-tape machine with O(n^c) space (§2.4) → InPSPACE: a valid coded machine without gate states, read-only input, output head never moving left, space c(|x|+2)^k; reason: a machine without gate states is a deterministic multi-tape Turing machine up to the endmarker conventions (p.20)
--   - reading: 'In particular, L⋆ ∈ BQP implies a positive answer to Open Problem 2, and hence implies every failure in Open Problem 1' → not a separate clause; reason: it is the case a = 1 of the main clause (n^c ≤ 2^{A log(n+2)} for large A) and the remark at the end of the proof (p.91)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 6.18, p.89

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_PolySampler
import Definitions.Def_QuantumKtSoI_PSPACEHard

open Classical

namespace QuantumKtSoI

/-- **Theorem 6.18** (Defect at the boundary exponent; Myrisiotis, STOC 2027 submission, held
version sha256 6616571c…, p.89). Fix a rational `a ≥ 1`. Suppose a machine of Definition 3.1
decides `L⋆`, with error at most `1/3`, on every sufficiently large input length `M`, within
`2^{A(log(M+2))^a}` steps on every branch, for a constant `A ≥ 1`. Then there is a rational
`η > 0` such that infinitely many pairs satisfy `Δ(u,v) > η(|u|+|v|)^{1/a}`.

**Formalization Note** The PSPACE-complete language `L⋆` of Theorem 2.4 is replaced by an arbitrary
language `L` that is PSPACE-hard under deterministic polynomial-time many-one reductions; `L⋆` is
one such language, so this specializes to the paper's statement. The paper's "In particular"
sentence is the case `a = 1` and the remark at the end of its proof, not a separate clause.
Logarithms are base 2. -/
theorem theorem_6_18 (G : GlueRoutines) (hG : G.Admissible) (L : Set (List Bool))
    (hL : PSPACEHard L) (a : ℚ) (ha : 1 ≤ a) (A : ℝ) (hA : 1 ≤ A)
    (hdec : ∃ B : CodedMachine, B.Valid ∧
      DecidesWithin B L fun M => (2 : ℝ) ^ (A * (Real.logb 2 ((M : ℝ) + 2)) ^ (a : ℝ))) :
    ∃ η : ℚ, 0 < η ∧
      {p : List Bool × List Bool |
        (η : ℝ) * ((p.1.length + p.2.length : ℕ) : ℝ) ^ (1 / (a : ℝ)) <
          (defect G p.1 p.2 : ℝ)}.Infinite := by sorry

end QuantumKtSoI
