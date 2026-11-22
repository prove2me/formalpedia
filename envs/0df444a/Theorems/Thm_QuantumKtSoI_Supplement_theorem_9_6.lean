-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_9_6
-- name    : QuantumKtSoI.Supplement.theorem_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:49:26.118053+00:00
-- url     : https://prove2.me/theorems/7ea72dd7-ea65-4435-b210-5b86e282dde0
-- title:
--   Theorem 9.6, p.120 — a universal gate set with computable entries for which $\mathrm{qKt}\le\mathrm{qKt}_{\mathcal G'}+B\log+B$ fails
-- statement:
--   There are a fixed finite universal gate set $\mathcal G'$, all of whose entries are computable, and an encoding satisfying (Enc) of Definition 9.3, such that:
--
--   1. for infinitely many positive integers $n$ there is $w_n\in\{0,1\}^{4n}$ with
--   $$\mathrm{qKt}(w_n)>3n,\qquad\mathrm{qKt}_{\mathcal G'}(w_n)\le 2n+O(\log(n+2));$$
--   2. some gate of $\mathcal G'$ has no exact block over $\mathcal G\cup\{T_m\}$ for any integer $m\ge2$, where $T_m=\mathrm{diag}(1,e^{2\pi i/2^m})$;
--   3. consequently, no constant $B$ makes $\mathrm{qKt}(y|x)\le\mathrm{qKt}_{\mathcal G'}(y|x)+B\log(|x|+|y|+2)+B$ hold for all strings $x,y$.
--
--   Here $\mathrm{qKt}_{\mathcal G'}$ is the measure defined by machines and descriptions whose gates come from $\mathcal G'$, and blocks are those of Definition 9.4.
--
--   This shows that the reverse logarithmic comparison between gate sets can fail even for computable entries.
--
--   **Formalization Note** The gate set is chosen after the glue routine set. The $O(\log(n+2))$ is one constant for all $n$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a finite set G′ of unitary gates with an encoding satisfying (Enc) → a finite indexed family of matrices with a natural-number name per gate (GateLib with Wf: arities ≥ 1, unitary, distinct names), and an injective encoding of the valid coded G′-machines; reason: a finite set with a fixed enumeration of its gate names, which (Enc) presupposes; G′-machines are represented as coded machines as in the base mission
--   - reading: (Enc): a polynomial-time parser recovers the complete finite structural description (no output format fixed) → a deterministic polynomial-time function maps every code to the standard structural record, the published encoding's layout with gate names from the fixed enumeration; reason: the record contains exactly the data Definition 9.3 lists; the paper leaves the format open
--   - reading: O(·) terms in the conclusion → one real constant K, chosen together with the named constant, multiplying each O-term; reason: the usual meaning of O(·) in an upper bound; the terms are at least 1, so one constant serves both
--   - reading: a complex number is computable if a deterministic Turing machine, given r, returns rational real and imaginary parts with error at most 2^{−r} → Mathlib's Computable for a function ℕ → ℤ × ℕ returning numerator and denominator, each part within 2^{−r}; reason: Turing computability is Mathlib's Computable; the error bound is applied to each part
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 9.6, pp.120–121; Definition 9.3, p.118; Definition 9.4, p.119; universal and computable, p.120

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_GDesc
import Definitions.Def_QuantumKtSoI_Supplement_ExactBlock

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 9.6** (Failure of gate comparison for computable entries; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, pp.120–121). There are a
fixed finite universal gate set `G′`, all of whose entries are computable, and an encoding
satisfying (Enc) of Definition 9.3, such that for infinitely many positive integers `n` there is
`w_n ∈ {0,1}^{4n}` with `qKt(w_n) > 3n` and `qKt_{G′}(w_n) ≤ 2n + O(log(n+2))`. Some gate of `G′`
has no exact block over `G ∪ {T_m}` for any integer `m ≥ 2`. Consequently, no constant `B` makes
`qKt(y|x) ≤ qKt_{G′}(y|x) + B log(|x|+|y|+2) + B` hold for all strings `x, y`.

**Formalization Note** `G` is any admissible glue routine set (p.24), fixed before the gate set, as
in the base mission. A gate set is a `GateLib` with `Wf` (arities `≥ 1`, unitary gates); the
encoding is of the valid coded `G′`-machines and satisfies `EncHyp`; `qKt_{G′}` is `qKtG`. The
`O(log(n+2))` is one constant `K` for all `n`. Logarithms are base 2. -/
theorem theorem_9_6 (G : GlueRoutines) (hG : G.Admissible) :
    ∃ L : GateLib, L.Wf ∧ L.Universal ∧ L.ComputableEntries ∧
      ∃ enc : {A : GCodedMachine L // A.Valid} → List Bool, EncHyp L enc ∧
        (∃ K : ℝ, ∀ N : ℕ, ∃ n ≥ N, 0 < n ∧ ∃ w : List Bool, w.length = 4 * n ∧
          3 * n < qKt G w [] ∧
          (qKtG L enc G w [] : ℝ) ≤ 2 * (n : ℝ) + K * Real.logb 2 ((n : ℝ) + 2)) ∧
        (∃ g : L.ι, ∀ m : ℕ, 2 ≤ m → ¬ExactBlock (nativeTm m) (L.amp g)) ∧
        ∀ B : ℝ, ¬∀ x y : List Bool,
          (qKt G y x : ℝ) ≤
            qKtG L enc G y x + B * Real.logb 2 ((x.length : ℝ) + y.length + 2) + B := by sorry

end QuantumKtSoI.Supplement
