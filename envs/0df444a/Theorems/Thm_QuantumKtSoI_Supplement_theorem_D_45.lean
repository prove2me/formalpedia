-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_45
-- name    : QuantumKtSoI.Supplement.theorem_D_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:54:57.20251+00:00
-- url     : https://prove2.me/theorems/dd4f9b1b-58ab-4c1a-a04e-6990fbfa3a97
-- title:
--   Theorem D.45, p.191 — $\mathrm{qKt}_{\mathcal G'}\le\mathrm{qKt}+\log(|x|+2)+A_1\log(\cdots)+A_1$ when the native gates have exact $\mathcal G'$-blocks
-- statement:
--   Let $\mathcal G'$ be a finite gate set with an encoding that satisfies (Enc), such that each of $H$, $X$, $\mathrm{CNOT}$, $\mathrm{SWAP}$ and $\mathrm{Toff}$ has an exact $\mathcal G'$-block (Definition 9.4). There is a constant $A_1$ such that, for all strings $x,y$, writing $\kappa=\mathrm{qKt}(y|x)$ and $L=\log(|x|+2)$,
--   $$\mathrm{qKt}_{\mathcal G'}(y|x)\le\kappa+L+A_1\log(\kappa+L+2)+A_1\le\kappa+\log(|x|+2)+O(\log(\kappa+2))+O(\log\log(|x|+4)).$$
--
--   This is the forward gate-set comparison: a gate set into which the native gates compile exactly costs at most a logarithmic term.
--
--   **Formalization Note** Logarithms are base $2$ and the values of the measures are read in $\mathbb R$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a finite set G′ of unitary gates with an encoding satisfying (Enc) → a finite indexed family of matrices with a natural-number name per gate (GateLib with Wf: arities ≥ 1, unitary, distinct names), and an injective encoding of the valid coded G′-machines; reason: a finite set with a fixed enumeration of its gate names, which (Enc) presupposes; G′-machines are represented as coded machines as in the base mission
--   - reading: (Enc): a polynomial-time parser recovers the complete finite structural description (no output format fixed) → a deterministic polynomial-time function maps every code to the standard structural record, the published encoding's layout with gate names from the fixed enumeration; reason: the record contains exactly the data Definition 9.3 lists; the paper leaves the format open
--   - reading: O(·) terms in the conclusion → one real constant K, chosen together with the named constant, multiplying each O-term; reason: the usual meaning of O(·) in an upper bound; the terms are at least 1, so one constant serves both
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.45, p.191; Definition 9.3, p.118; Definition 9.4, p.119

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_GDesc
import Definitions.Def_QuantumKtSoI_Supplement_ExactBlock

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.45** (Gate sets into which `G` compiles exactly; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.191). Let `G′` be a finite
gate set with an encoding that satisfies (Enc), such that each of `H, X, CNOT, SWAP, Toff` has an
exact `G′`-block. There is a constant `A₁` such that, for all strings `x, y`, writing
`κ = qKt(y|x)` and `L = log(|x|+2)`,
`qKt_{G′}(y|x) ≤ κ + L + A₁ log(κ + L + 2) + A₁ ≤ κ + log(|x|+2) + O(log(κ+2)) + O(log log(|x|+4))`.

**Formalization Note** `G` is any admissible glue routine set (p.24). The gate set is a `GateLib`
with `Wf`, the encoding satisfies `EncHyp`, blocks are those of Definition 9.4 (`ExactBlock`), and
`qKt_{G′}` is `qKtG`. The two `O(·)` terms are one constant `K` chosen with `A₁`. Logarithms are
base 2. -/
theorem theorem_D_45 (G : GlueRoutines) (hG : G.Admissible) (L : GateLib) (hL : L.Wf)
    (enc : {A : GCodedMachine L // A.Valid} → List Bool) (hE : EncHyp L enc)
    (hblk : ∀ g : Gate, ExactBlock L (Gate.amp g)) :
    ∃ A₁ K : ℝ, ∀ x y : List Bool,
      (qKtG L enc G y x : ℝ) ≤
          (qKt G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            A₁ * Real.logb 2 ((qKt G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) + 2) + A₁ ∧
        (qKt G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            A₁ * Real.logb 2 ((qKt G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) + 2) + A₁ ≤
          (qKt G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            K * Real.logb 2 ((qKt G y x : ℝ) + 2) +
            K * Real.logb 2 (Real.logb 2 ((x.length : ℝ) + 4)) := by sorry

end QuantumKtSoI.Supplement
