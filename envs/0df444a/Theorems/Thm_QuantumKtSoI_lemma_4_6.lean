-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_4_6
-- name    : QuantumKtSoI.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:22.706088+00:00
-- url     : https://prove2.me/theorems/cddfe4e8-06f3-4f77-87b6-2ee17fc541d6
-- title:
--   Lemma 4.6 — prefix-free counting
-- statement:
--   Let $1/2<\alpha\le1$, let $s\ge0$ be real and let $u$ be a string. At most $2^{\lfloor s\rfloor}$ strings $w$ have $\mathrm{qKt}_\alpha(w\mid u)\le s$; in particular, with $u=\epsilon$, at most $2^{\lfloor s\rfloor}$ strings $w$ have $\mathrm{qKt}_\alpha(w)\le s$. Consequently, for every integer $n\ge0$, if $r$ is uniform on $\{0,1\}^n$,
--   $$\Pr\big[\mathrm{qKt}_\alpha(r)\le n/2\big]\ \le\ 2^{\lfloor n/2\rfloor-n}.$$
--
--   The counting bound says that, even given a condition, most strings have high complexity; the lower bounds use it repeatedly.
--
--   Differences from the source:
--   - generalization: qKt_α for the paper's fixed glue routines → qKt_α for every glue-routine set G, admissible or not; reason: the bound uses only prefix-freeness of descriptions and that a description's output masses sum to at most 1, which hold for every G; the paper's routine set is one instance
--   - reading: AMP loading, comparison and copy routines described only by their behaviour (pp.25–26, p.29) → routines pinned step by step in ampCore (loading sweep of 2|x|+3 steps; the two comparison heads return together; the copy routine returns copy i's output head, then copies in one sweep); reason: the paper leaves these routines unspecified beyond the stated behaviour; this is the most direct implementation of it
--   - reading: a standard injective binary encoding ⌜A⌝ of machines (p.23) → the fixed encoding CodedMachine.encode, every field written as a self-delimiting number in a fixed order; reason: the paper fixes the encoding only by its contents; by Corollary 9.5 (p.119) admissible encodings change qKt by O(log)
--   - encoding: P_M(x;t,w) = Σ ‖ψ_ρ‖² over ρ ∈ Rᵗ with ψ_ρ ≠ 0, st(ρ) final, out(ρ) = w (Definition 3.4) → Σ_{ρ ∈ recSeqs} Σ_{C final, output C = w} |ψ_ρ(C)|²; reason: equal by Lemma 3.3(iii): the support of a nonzero branch vector shares state and output; sequences outside recSeqs have ψ_ρ = 0
--   - encoding: descriptions e ∈ E charged |e| (Definition 3.6) → e : Desc charged |Desc.bits e|; reason: by Lemma 3.7 each string of E has exactly one parse, so ranging over Desc is ranging over E
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
--   - encoding: qKt as a minimum of |e| + ⌈log t⌉ (Definition 4.1) → ℕ-valued sInf of the feasible costs, ⌈log t⌉ = Nat.clog 2 t; reason: the feasible set is nonempty (LIT(y), p.41), so the sInf is the minimum; Nat.clog 2 t = ⌈log₂ t⌉ for t ≥ 1
--   - encoding: 'at most 2^⌊s⌋ strings' and 'the probability over uniform r' → Set.encard ≤ 2^⌊s⌋ and a count over Fin n → Bool divided by 2ⁿ; reason: the same quantities; encard also asserts finiteness
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 4.6, p.43

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 4.6** (Prefix-free counting; Myrisiotis, STOC 2027 submission, held version sha256
6616571c…, p.43). Let `1/2 < α ≤ 1`, let `s ≥ 0` be real, and let `u` be a string. At most `2^⌊s⌋`
strings `w` have `qKt_α(w|u) ≤ s`; in particular, with `u = ε`, at most `2^⌊s⌋` strings `w` have
`qKt_α(w) ≤ s`. Consequently, for every integer `n ≥ 0`, if `r` is uniform on `{0,1}ⁿ`, the
probability that `qKt_α(r) ≤ n/2` is at most `2^{⌊n/2⌋−n}`.

**Formalization Note** The counts are `Set.encard` (so finiteness is part of the claim) and the
probability is a count over `Fin n → Bool` divided by `2ⁿ`. The statement holds for every set of
glue routines `G`. -/
theorem lemma_4_6 (G : GlueRoutines) (α : ℝ) (hα₁ : 1 / 2 < α) (hα₂ : α ≤ 1) :
    (∀ s : ℝ, 0 ≤ s → ∀ u : List Bool,
        {w : List Bool | (qKtRho G α w u : ℝ) ≤ s}.encard ≤ 2 ^ ⌊s⌋₊) ∧
      (∀ s : ℝ, 0 ≤ s → {w : List Bool | (qKtRho G α w [] : ℝ) ≤ s}.encard ≤ 2 ^ ⌊s⌋₊) ∧
      ∀ n : ℕ,
        ((Finset.univ.filter fun r : Fin n → Bool =>
            (qKtRho G α (List.ofFn r) [] : ℝ) ≤ (n : ℝ) / 2).card : ℝ) / 2 ^ n ≤
          (2 : ℝ) ^ (((n / 2 : ℕ) : ℤ) - n) := by sorry

end QuantumKtSoI
