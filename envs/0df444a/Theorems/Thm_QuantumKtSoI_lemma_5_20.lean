-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_5_20
-- name    : QuantumKtSoI.lemma_5_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:36.907858+00:00
-- url     : https://prove2.me/theorems/6eec6813-162b-4879-99f9-b654af699615
-- title:
--   Lemma 5.20 — exhaustive estimation
-- statement:
--   Fix admissible glue routines and a rational $c>0$, written $c=p_c/q_c$ in lowest terms. There are a machine $\mathrm{Exh}_c$ and a constant $c_E$ such that for all strings $u,w$ and every integer $r\ge1$, on input $\langle u,\langle w,1^r\rangle\rangle$ the machine $\mathrm{Exh}_c$ halts within $2^{c_E(|u|+1)}(|w|+r+2)^{c_E}$ steps and, with probability at least $1-2^{-r}$, outputs (the binary expansion of the numerator $N$ of) a rational number $v=N/q_c$ with
--   $$\mathrm{qKt}^{(c)}(u\mid w)-c\lceil\log(|w|+2)\rceil-c_E\ \le\ v\ \le\ \mathrm{qKt}^{(c)}(u\mid w).$$
--   For $c=1$, $q_c=1$ and the output is an integer.
--
--   Exhaustive search estimates conditional complexity of short strings efficiently; the separator of Lemma 5.21 combines such estimates.
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
--   - reading: 'outputs a rational number v' → outputs b(N), read as v = N/q_c with q_c the denominator of c in lowest terms; reason: the encoding used in the proof (p.70: costs are written by their numerators over q_c)
--   - encoding: qKt^{(c)} as a minimum (Definition 4.2) → real sInf of the feasible costs; reason: the feasible set is nonempty and below any feasible cost takes finitely many values, so the infimum is the minimum (p.41)
--   - encoding: the probability of the event 'v lies in the window' → the sum of P over the outputs b(N) with N ≤ ⌊q_c·qKt^{(c)}⌋ and N/q_c in the window; reason: b is injective and every N with N/q_c ≤ qKt^{(c)} is in that range
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 5.20, p.69; output encoding from its proof, p.70

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 5.20** (Exhaustive estimation; Myrisiotis, STOC 2027 submission, held version sha256
6616571c…, p.69). Let `c > 0` be rational. There are a machine `Exh_c` and a constant `c_E`,
depending on `c`, such that, for all strings `u, w` and every integer `r ≥ 1`, on input
`⟨u,⟨w,1ʳ⟩⟩` the machine `Exh_c` halts within `2^{c_E(|u|+1)} (|w|+r+2)^{c_E}` steps and outputs a
rational number `v` with `qKt^{(c)}(u|w) − c⌈log(|w|+2)⌉ − c_E ≤ v ≤ qKt^{(c)}(u|w)` with
probability at least `1 − 2^{−r}`. For `c = 1` we write `Exh = Exh_1`, whose output is an integer.

**Formalization Note** The output encoding is the one of the proof (p.70): with `c = p_c/q_c` in
lowest terms, the output `b(N)` stands for `v = N/q_c`; the probability of the event is the sum of
`P` over the outputs `b(N)` with `N/q_c` in the window (all such `N` are below `q_c·qKt^{(c)} + 1`).
For `c = 1` we have `q_c = 1`, so `v = N` is an integer. `Exh_c` is a valid coded machine. -/
theorem lemma_5_20 (G : GlueRoutines) (hG : G.Admissible) (c : ℚ) (hc : 0 < c) :
    ∃ Exh : CodedMachine, Exh.Valid ∧ ∃ cE : ℝ, ∀ (u w : List Bool) (r : ℕ), 1 ≤ r →
      Exh.toMachine.HaltsWithin (pair u (pair w (ones r)))
          ⌊(2 : ℝ) ^ (cE * (u.length + 1)) * ((w.length + r + 2 : ℝ)) ^ cE⌋₊ ∧
        1 - (2 : ℝ) ^ (-(r : ℤ)) ≤
          ∑ N ∈ (Finset.range (⌊(c.den : ℝ) * qKtCharge G c u w⌋₊ + 1)).filter (fun N : ℕ =>
              qKtCharge G c u w - (c : ℝ) * Nat.clog 2 (w.length + 2) - cE ≤ (N : ℝ) / c.den ∧
                (N : ℝ) / c.den ≤ qKtCharge G c u w),
            Exh.toMachine.outputProbR (pair u (pair w (ones r)))
              ((2 : ℝ) ^ (cE * (u.length + 1)) * ((w.length + r + 2 : ℝ)) ^ cE) (bin N) := by sorry

end QuantumKtSoI
