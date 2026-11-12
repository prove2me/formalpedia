-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_5_4
-- name    : QuantumKtSoI.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:10.577407+00:00
-- url     : https://prove2.me/theorems/7c59b733-c35c-4d47-ae56-e63bed4b9f4c
-- title:
--   Lemma 5.4 — re-encoding
-- statement:
--   Fix admissible glue routines. Let $F$ be a fixed machine without gate states that, on every input $\langle\langle\epsilon,w\rangle,h\rangle$, halts within $c_F(|h|+|w|+1)$ steps with output $\phi(h,w)$ with probability one. There is a constant $c'_F$ such that
--   $$\mathrm{qKt}(\phi(h,w))\ \le\ \mathrm{qKt}(w)+|h|+3\log(|h|+2)+c'_F\quad\text{for all strings } h,w.$$
--
--   A fixed deterministic post-processing with an explicit header costs only the header and a logarithmic term; the lemma converts between pairing and concatenation encodings.
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
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 5.4, p.52

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 5.4** (Re-encoding; Myrisiotis, STOC 2027 submission, held version sha256 6616571c…,
p.52). Let `F` be a fixed machine without gate states that, on every input `⟨⟨ε,w⟩,h⟩`, halts within
`c_F(|h|+|w|+1)` steps with output `ϕ(h,w)` with probability one. There is a constant `c'_F` such
that `qKt(ϕ(h,w)) ≤ qKt(w) + |h| + 3 log(|h|+2) + c'_F` for all strings `h, w`.

**Formalization Note** `F` is a valid coded machine without gate states; the step bound is read at
its floor (p.22). Logarithms are base 2. -/
theorem lemma_5_4 (G : GlueRoutines) (hG : G.Admissible) (F : CodedMachine) (hF : F.Valid)
    (hF₀ : F.GateFree) (φ : List Bool → List Bool → List Bool) (cF : ℝ)
    (hφ : ∀ h w : List Bool,
      F.toMachine.HaltsWithin (pair (pair [] w) h) ⌊cF * (h.length + w.length + 1)⌋₊ ∧
        F.toMachine.outputProbR (pair (pair [] w) h) (cF * (h.length + w.length + 1)) (φ h w) = 1) :
    ∃ c'F : ℝ, ∀ h w : List Bool,
      (qKt G (φ h w) [] : ℝ) ≤ qKt G w [] + h.length + 3 * Real.logb 2 (h.length + 2) + c'F := by sorry

end QuantumKtSoI
