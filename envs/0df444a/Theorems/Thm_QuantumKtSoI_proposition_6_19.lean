-- Prove2me | Theorems.Thm_QuantumKtSoI_proposition_6_19
-- name    : QuantumKtSoI.proposition_6_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:50.403472+00:00
-- url     : https://prove2.me/theorems/b6152fbf-9ec4-4847-b2cd-1d625107419b
-- title:
--   Proposition 6.19 — one classical sampler from linear defect
-- statement:
--   Fix admissible glue routines. There is one classical polynomial-time sampler $S$, outputting two $n$-bit strings on input $1^n$, with the following property. If some $\eta>0$ satisfies $\Delta(u,v)>\eta(|u|+|v|)$ for infinitely many pairs, then for every real $C\ge1$ there is an integer $d_C\ge1$ such that
--   $$\Pr_{(X,Y)\sim S(1^n)}\big[\Delta(X,Y)>C\log(2n+2)\big]\ \ge\ n^{-d_C}$$
--   for infinitely many $n$. The sampler is independent of $\eta$ and $C$, and its running time is polynomial on every branch.
--
--   Together with Theorem 6.18, a positive linear defect yields a fixed classical sampler of logarithmic violations.
--
--   Differences from the source:
--   - generalization: the paper's glue routines, fixed once and for all and described only by their properties (p.24) → every admissible glue-routine set G (GlueRoutines.Admissible: local rules of Definition 3.1, exit within c₀(|x|+|u|+|v|+ℓ+1) steps with the glue map written and all heads on cell 0); reason: the proofs use only the p.24 properties, so the paper's routine set is one admissible instance
--   - reading: AMP loading, comparison and copy routines described only by their behaviour (pp.25–26, p.29) → routines pinned step by step in ampCore (loading sweep of 2|x|+3 steps; the two comparison heads return together; the copy routine returns copy i's output head, then copies in one sweep); reason: the paper leaves these routines unspecified beyond the stated behaviour; this is the most direct implementation of it
--   - reading: a standard injective binary encoding ⌜A⌝ of machines (p.23) → the fixed encoding CodedMachine.encode, every field written as a self-delimiting number in a fixed order; reason: the paper fixes the encoding only by its contents; by Corollary 9.5 (p.119) admissible encodings change qKt by O(log)
--   - encoding: P_M(x;t,w) = Σ ‖ψ_ρ‖² over ρ ∈ Rᵗ with ψ_ρ ≠ 0, st(ρ) final, out(ρ) = w (Definition 3.4) → Σ_{ρ ∈ recSeqs} Σ_{C final, output C = w} |ψ_ρ(C)|²; reason: equal by Lemma 3.3(iii): the support of a nonzero branch vector shares state and output; sequences outside recSeqs have ψ_ρ = 0
--   - encoding: descriptions e ∈ E charged |e| (Definition 3.6) → e : Desc charged |Desc.bits e|; reason: by Lemma 3.7 each string of E has exactly one parse, so ranging over Desc is ranging over E
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
--   - encoding: qKt as a minimum of |e| + ⌈log t⌉ (Definition 4.1) → ℕ-valued sInf of the feasible costs, ⌈log t⌉ = Nat.clog 2 t; reason: the feasible set is nonempty (LIT(y), p.41), so the sInf is the minimum; Nat.clog 2 t = ⌈log₂ t⌉ for t ≥ 1
--   - reading: a classical polynomial-time sampler (p.51: a machine of Definition 3.1 whose only qubit operations are fair-coin draws) → PolySampler: a §2.1 probabilistic Turing machine with all-branch deadline c(n+2)^k; reason: the two models sample the same families in polynomial time (a coin draw is one coin step; Proposition 9.8)
--   - encoding: per-tape alphabets of a §2.1 probabilistic Turing machine, each containing 0, 1 and a distinct blank (p.13) → one finite alphabet Γ shared by all tapes, containing 0, 1 and a distinct blank; reason: per-tape alphabets merge into their union and a shared alphabet is the case of equal per-tape alphabets, so the class of samplers is unchanged
--   - reading: 'outputting two n-bit strings' → one output of length 2n read as XY = ⟨X, Y⟩; reason: the pairing of equal-length strings is their concatenation (§2.1; p.95)
--   - encoding: 'for infinitely many n' and n^{−d} → ∀ N, ∃ n ≥ N and 1/nᵈ; reason: the same statements
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Proposition 6.19, p.91

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_PolySampler
import Definitions.Def_QuantumKtSoI_PSPACEHard

open Classical

namespace QuantumKtSoI

/-- **Proposition 6.19** (One classical sampler from linear defect; Myrisiotis, STOC 2027
submission, held version sha256 6616571c…, p.91). There is one classical polynomial-time sampler
`S`, outputting two `n`-bit strings on input `1ⁿ`, with the following property. If some `η > 0`
satisfies `Δ(u,v) > η(|u|+|v|)` for infinitely many pairs, then, for every real `C ≥ 1`, there is
an integer `d_C ≥ 1` such that `Pr_{(X,Y)∼S(1ⁿ)}[Δ(X,Y) > C log(2n+2)] ≥ n^{−d_C}` for infinitely
many `n`. The sampler is independent of `η` and `C`, and its running time is polynomial on every
branch.

**Formalization Note** The sampler is a `PolySampler` (a §2.1 probabilistic Turing machine with an
all-branch polynomial deadline and `2n`-bit outputs `XY = ⟨X,Y⟩`), chosen before `η` and `C`.
"Infinitely many `n`" is `∀ N, ∃ n ≥ N`; `n^{−d}` is `1/nᵈ`. Logarithms are base 2. -/
theorem proposition_6_19 (G : GlueRoutines) (hG : G.Admissible) :
    ∃ S : PolySampler,
      (∃ η : ℝ, 0 < η ∧
        {p : List Bool × List Bool |
          η * ((p.1.length + p.2.length : ℕ) : ℝ) < (defect G p.1 p.2 : ℝ)}.Infinite) →
      ∀ C : ℝ, 1 ≤ C → ∃ d : ℕ, 1 ≤ d ∧ ∀ N : ℕ, ∃ n ≥ N,
        1 / (n : ℝ) ^ d ≤
          S.prob n fun X Y => C * Real.logb 2 (2 * n + 2) < (defect G X Y : ℝ) := by sorry

end QuantumKtSoI
