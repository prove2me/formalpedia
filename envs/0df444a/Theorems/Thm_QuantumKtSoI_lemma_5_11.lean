-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_5_11
-- name    : QuantumKtSoI.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:32.689611+00:00
-- url     : https://prove2.me/theorems/f52ad794-5fa6-4146-b19b-11be40224cb4
-- title:
--   Lemma 5.11 — padding
-- statement:
--   Fix admissible glue routines. There is a positive integer $c_{\mathrm{pad}}$ such that for all strings $v$ and integers $\lambda>|v|$,
--   $$\mathrm{qKt}(v)-c_{\mathrm{pad}}\ \le\ \mathrm{qKt}(\mathrm{pad}_\lambda(v))\ \le\ \mathrm{qKt}(v)+3\lceil\log(\lambda+2)\rceil+c_{\mathrm{pad}} .$$
--
--   Padding changes complexity only logarithmically; it turns violations on strings of different lengths into violations on equal-length strings.
--
--   Differences from the source:
--   - generalization: the paper's glue routines, fixed once and for all and described only by their properties (p.24) → every admissible glue-routine set G (GlueRoutines.Admissible: local rules of Definition 3.1, exit within c₀(|x|+|u|+|v|+ℓ+1) steps with the glue map written and all heads on cell 0); reason: the proofs use only the p.24 properties, so the paper's routine set is one admissible instance
--   - reading: AMP loading, comparison and copy routines described only by their behaviour (pp.25–26, p.29) → routines pinned step by step in ampCore (loading sweep of 2|x|+3 steps; the two comparison heads return together; the copy routine returns copy i's output head, then copies in one sweep); reason: the paper leaves these routines unspecified beyond the stated behaviour; this is the most direct implementation of it
--   - reading: a standard injective binary encoding ⌜A⌝ of machines (p.23) → the fixed encoding CodedMachine.encode, every field written as a self-delimiting number in a fixed order; reason: the paper fixes the encoding only by its contents; by Corollary 9.5 (p.119) admissible encodings change qKt by O(log)
--   - encoding: P_M(x;t,w) = Σ ‖ψ_ρ‖² over ρ ∈ Rᵗ with ψ_ρ ≠ 0, st(ρ) final, out(ρ) = w (Definition 3.4) → Σ_{ρ ∈ recSeqs} Σ_{C final, output C = w} |ψ_ρ(C)|²; reason: equal by Lemma 3.3(iii): the support of a nonzero branch vector shares state and output; sequences outside recSeqs have ψ_ρ = 0
--   - encoding: descriptions e ∈ E charged |e| (Definition 3.6) → e : Desc charged |Desc.bits e|; reason: by Lemma 3.7 each string of E has exactly one parse, so ranging over Desc is ranging over E
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
--   - encoding: qKt as a minimum of |e| + ⌈log t⌉ (Definition 4.1) → ℕ-valued sInf of the feasible costs, ⌈log t⌉ = Nat.clog 2 t; reason: the feasible set is nonempty (LIT(y), p.41), so the sInf is the minimum; Nat.clog 2 t = ⌈log₂ t⌉ for t ≥ 1
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 5.11, p.60

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 5.11** (Padding; Myrisiotis, STOC 2027 submission, held version sha256 6616571c…,
p.60). There is a positive integer `c_pad` such that
`qKt(v) − c_pad ≤ qKt(pad_λ(v)) ≤ qKt(v) + 3⌈log(λ+2)⌉ + c_pad` for all `v` and `λ > |v|`.

**Formalization Note** `⌈log(λ+2)⌉` is `Nat.clog 2 (λ+2)`; the inequalities are in `ℤ`. -/
theorem lemma_5_11 (G : GlueRoutines) (hG : G.Admissible) :
    ∃ cpad : ℕ, 0 < cpad ∧ ∀ (v : List Bool) (lam : ℕ), v.length < lam →
      (qKt G v [] : ℤ) - cpad ≤ qKt G (pad lam v) [] ∧
        (qKt G (pad lam v) [] : ℤ) ≤ qKt G v [] + 3 * Nat.clog 2 (lam + 2) + cpad := by sorry

end QuantumKtSoI
