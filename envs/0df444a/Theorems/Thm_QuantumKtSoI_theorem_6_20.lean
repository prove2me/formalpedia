-- Prove2me | Theorems.Thm_QuantumKtSoI_theorem_6_20
-- name    : QuantumKtSoI.theorem_6_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:39.595757+00:00
-- url     : https://prove2.me/theorems/d4045a94-d844-4fb7-bc0c-239506250665
-- title:
--   Theorem 6.20 with Theorem 6.21 — one classical sampler exceeds a symmetry defect of $C\log(2n+2)$ for every $C\ge1$
-- statement:
--   Admissible glue routines exist, and for every admissible set the following holds. There is one classical polynomial-time sampler $S$, outputting two $n$-bit strings on every input $1^n$, such that:
--   1. (Theorem 6.20) for every real $C\ge1$ there is an integer $d_C\ge1$ with
--   $$\Pr_{(X,Y)\sim S(1^n)}\big[\Delta(X,Y)>C\log(2n+2)\big]\ >\ n^{-d_C}\quad\text{for infinitely many } n;$$
--   2. (Theorem 6.21) for every conditional cost function $\mu$ (a real value $\mu(v\mid u)$ for all strings $u,v$) with $|\mu(v\mid u)-\mathrm{qKt}(v\mid u)|\le B_\mu\log(|u|+|v|+2)+B_\mu$ for all $u,v$ and some $B_\mu\ge0$, and every real $C\ge1$, there is an integer $d_{\mu,C}\ge1$ with
--   $$\Pr_{(X,Y)\sim S(1^n)}\big[\Delta_\mu(X,Y)>C\log(2n+2)\big]\ >\ n^{-d_{\mu,C}}\quad\text{for infinitely many } n,$$
--   where $\Delta_\mu(x,y)=\mu(x)+\mu(y\mid x)-\mu(\langle x,y\rangle)$ and $\mu(v)=\mu(v\mid\epsilon)$.
--
--   The sampler is independent of $C$ and $\mu$, and its running time is polynomial on every branch. This is the unconditional failure of symmetry of information for quantum Kt complexity on average over a fixed classical polynomial-time samplable distribution, for every logarithmic error coefficient.
--
--   Differences from the source:
--   - generalization: the paper's glue routines, fixed once and for all and described only by their properties (p.24) → the conjunction (∃ G admissible) ∧ ∀ G admissible, ∃ S, …, the sampler chosen after the routine set; reason: the proofs use only the p.24 properties, so the paper's routine set is one admissible instance
--   - generalization: Theorem 6.20 for qKt → also the clause of Theorem 6.21 for every conditional cost function within B log + B of qKt; reason: Theorem 6.21 is the paper's own statement for the same sampler; µ = qKt, B = 0 gives Theorem 6.20
--   - reading: AMP loading, comparison and copy routines described only by their behaviour (pp.25–26, p.29) → routines pinned step by step in ampCore (loading sweep of 2|x|+3 steps; the two comparison heads return together; the copy routine returns copy i's output head, then copies in one sweep); reason: the paper leaves these routines unspecified beyond the stated behaviour; this is the most direct implementation of it
--   - reading: a standard injective binary encoding ⌜A⌝ of machines (p.23) → the fixed encoding CodedMachine.encode, every field written as a self-delimiting number in a fixed order; reason: the paper fixes the encoding only by its contents; by Corollary 9.5 (p.119) admissible encodings change qKt by O(log)
--   - encoding: P_M(x;t,w) = Σ ‖ψ_ρ‖² over ρ ∈ Rᵗ with ψ_ρ ≠ 0, st(ρ) final, out(ρ) = w (Definition 3.4) → Σ_{ρ ∈ recSeqs} Σ_{C final, output C = w} |ψ_ρ(C)|²; reason: equal by Lemma 3.3(iii): the support of a nonzero branch vector shares state and output; sequences outside recSeqs have ψ_ρ = 0
--   - encoding: descriptions e ∈ E charged |e| (Definition 3.6) → e : Desc charged |Desc.bits e|; reason: by Lemma 3.7 each string of E has exactly one parse, so ranging over Desc is ranging over E
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
--   - encoding: qKt as a minimum of |e| + ⌈log t⌉ (Definition 4.1) → ℕ-valued sInf of the feasible costs, ⌈log t⌉ = Nat.clog 2 t; reason: the feasible set is nonempty (LIT(y), p.41), so the sInf is the minimum; Nat.clog 2 t = ⌈log₂ t⌉ for t ≥ 1
--   - reading: a classical polynomial-time sampler (p.51: a machine of Definition 3.1 whose only qubit operations are fair-coin draws) → PolySampler: a §2.1 probabilistic Turing machine with all-branch deadline c(n+2)^k; reason: the two models sample the same families in polynomial time (a coin draw is one coin step; Proposition 9.8)
--   - encoding: per-tape alphabets of a §2.1 probabilistic Turing machine, each containing 0, 1 and a distinct blank (p.13) → one finite alphabet Γ shared by all tapes, containing 0, 1 and a distinct blank; reason: per-tape alphabets merge into their union and a shared alphabet is the case of equal per-tape alphabets, so the class of samplers is unchanged
--   - reading: 'outputting two n-bit strings' → one output of length 2n read as XY = ⟨X, Y⟩; reason: the pairing of equal-length strings is their concatenation (§2.1; p.95)
--   - encoding: µ(v|u) ∈ ℝ ∪ {∞} → µ : List Bool → List Bool → ℝ; reason: the comparison hypothesis forces µ to be finite-valued (p.95)
--   - encoding: 'for infinitely many n' and n^{−d} → ∀ N, ∃ n ≥ N and 1/nᵈ; reason: the same statements
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 6.20, p.92; Theorem 6.21, p.95

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_PolySampler
import Definitions.Def_QuantumKtSoI_PSPACEHard

open Classical

namespace QuantumKtSoI

/-- **Theorem 6.20** (Classical sampling of symmetry violations; native case of Theorem 1.1;
Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission,
held version sha256 6616571c…, p.92), together with **Theorem 6.21** (The same classical sampler
under logarithmic comparison, p.95).

There is one classical polynomial-time sampler `S`, outputting two `n`-bit strings on every input
`1ⁿ`, such that, for every real `C ≥ 1`, there is an integer `d_C ≥ 1` with
`Pr_{(X,Y)∼S(1ⁿ)}[Δ(X,Y) > C log(2n+2)] > n^{−d_C}` for infinitely many `n`. The sampler is
independent of `C`, and its running time is polynomial on every branch. (Theorem 6.21) For every
conditional cost function `µ` with `|µ(v|u) − qKt(v|u)| ≤ B_µ log(|u|+|v|+2) + B_µ` for all `u, v`
and some `B_µ ≥ 0`, and every real `C ≥ 1`, there is an integer `d_{µ,C} ≥ 1` with
`Pr_{(X,Y)∼S(1ⁿ)}[Δ_µ(X,Y) > C log(2n+2)] > n^{−d_{µ,C}}` for infinitely many `n`, for the same `S`.

**Formalization Note** The paper's glue routines are fixed only by their properties (p.24); the
statement asserts that admissible routine sets exist and that the conclusion holds for every one
of them, with `S` chosen after the routine set and before `C` and `µ`. The sampler is a
`PolySampler` (a §2.1 probabilistic Turing machine with an all-branch deadline `c(n+2)^k` whose
`2n`-bit output `XY` is the pair `⟨X,Y⟩`). "Infinitely many `n`" is `∀ N, ∃ n ≥ N`; `n^{−d}` is
`1/nᵈ`; `µ` is real-valued (the comparison hypothesis forces finite values);
`Δ_µ(x,y) = µ(x) + µ(y|x) − µ(⟨x,y⟩)` with `µ(v) = µ(v|ε)`, and `µ v u` stands for `µ(v|u)`.
Logarithms are base 2. -/
theorem theorem_6_20 :
    (∃ G : GlueRoutines, G.Admissible) ∧
      ∀ G : GlueRoutines, G.Admissible →
        ∃ S : PolySampler,
          (∀ C : ℝ, 1 ≤ C → ∃ d : ℕ, 1 ≤ d ∧ ∀ N : ℕ, ∃ n ≥ N,
            1 / (n : ℝ) ^ d <
              S.prob n fun X Y => C * Real.logb 2 (2 * n + 2) < (defect G X Y : ℝ)) ∧
          ∀ μ : List Bool → List Bool → ℝ,
            (∃ B : ℝ, 0 ≤ B ∧ ∀ u v : List Bool,
              |μ v u - qKt G v u| ≤ B * Real.logb 2 (u.length + v.length + 2) + B) →
            ∀ C : ℝ, 1 ≤ C → ∃ d : ℕ, 1 ≤ d ∧ ∀ N : ℕ, ∃ n ≥ N,
              1 / (n : ℝ) ^ d <
                S.prob n fun X Y => C * Real.logb 2 (2 * n + 2) < μ X [] + μ Y X - μ (pair X Y) [] := by sorry

end QuantumKtSoI
