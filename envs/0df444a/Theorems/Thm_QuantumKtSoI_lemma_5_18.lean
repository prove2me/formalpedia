-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_5_18
-- name    : QuantumKtSoI.lemma_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:36.161846+00:00
-- url     : https://prove2.me/theorems/59b18ecc-c276-4e41-80fa-da9fa9504341
-- title:
--   Lemma 5.18 — conditional subadditivity
-- statement:
--   Fix admissible glue routines. There is a constant $c_S\ge1$ such that for all strings $w,x,y$,
--   $$\mathrm{qKt}(xy\mid w)\ \le\ \mathrm{qKt}(x\mid w)+\mathrm{qKt}(y\mid wx)+\log(|w|+2)+c_S ,$$
--   where $xy$ and $wx$ are concatenations.
--
--   Producing $x$ given $w$ and then $y$ given $wx$ produces $xy$ given $w$; the separator and the identity (8) for conditional defects rest on this bound.
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
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 5.18, p.65

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 5.18** (Conditional subadditivity; Myrisiotis, STOC 2027 submission, held version
sha256 6616571c…, p.65). There is a constant `c_S ≥ 1` such that, for all strings `w, x, y`,
`qKt(xy|w) ≤ qKt(x|w) + qKt(y|wx) + log(|w|+2) + c_S`.

**Formalization Note** `xy` and `wx` are concatenations, as in the paper. -/
theorem lemma_5_18 (G : GlueRoutines) (hG : G.Admissible) :
    ∃ cS : ℝ, 1 ≤ cS ∧ ∀ w x y : List Bool,
      (qKt G (x ++ y) w : ℝ) ≤ qKt G x w + qKt G y (w ++ x) + Real.logb 2 (w.length + 2) + cS := by sorry

end QuantumKtSoI
