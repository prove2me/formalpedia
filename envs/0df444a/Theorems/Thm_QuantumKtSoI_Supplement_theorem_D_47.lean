-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_47
-- name    : QuantumKtSoI.Supplement.theorem_D_47
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:56:27.028813+00:00
-- url     : https://prove2.me/theorems/ac755d98-fa31-4697-8db6-4e6e74f67570
-- title:
--   Theorem D.47, p.193 — $\mathrm{qKt}\le\mathrm{qKt}_{\mathcal G'}+\log(|x|+2)+A_2\log(\cdots)+A_2$ when the gates of $\mathcal G'$ have real-encoded $\mathcal G$-blocks
-- statement:
--   Let $\mathcal G'$ be a finite gate set with an encoding that satisfies (Enc), such that every gate of $\mathcal G'$ has a real-encoded $\mathcal G$-block (Definition 9.4); an exact $\mathcal G$-block suffices. There is a constant $A_2$ such that, for all strings $x,y$, writing $\kappa'=\mathrm{qKt}_{\mathcal G'}(y|x)$ and $L=\log(|x|+2)$,
--   $$\mathrm{qKt}(y|x)\le\kappa'+L+A_2\log(\kappa'+L+2)+A_2\le\kappa'+\log(|x|+2)+O(\log(\kappa'+2))+O(\log\log(|x|+4)).$$
--
--   This is the reverse gate-set comparison for gate sets that compile into the native set.
--
--   **Formalization Note** Logarithms are base $2$ and the values of the measures are read in $\mathbb R$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a finite set G′ of unitary gates with an encoding satisfying (Enc) → a finite indexed family of matrices with a natural-number name per gate (GateLib with Wf: arities ≥ 1, unitary, distinct names), and an injective encoding of the valid coded G′-machines; reason: a finite set with a fixed enumeration of its gate names, which (Enc) presupposes; G′-machines are represented as coded machines as in the base mission
--   - reading: (Enc): a polynomial-time parser recovers the complete finite structural description (no output format fixed) → a deterministic polynomial-time function maps every code to the standard structural record, the published encoding's layout with gate names from the fixed enumeration; reason: the record contains exactly the data Definition 9.3 lists; the paper leaves the format open
--   - reading: O(·) terms in the conclusion → one real constant K, chosen together with the named constant, multiplying each O-term; reason: the usual meaning of O(·) in an upper bound; the terms are at least 1, so one constant serves both
--   - reading: "every gate of G′ has a real-encoded G-block; by Lemma D.41(iv), an exact G-block suffices" → hypothesis: every gate of G′ has a real-encoded G-block or an exact G-block; reason: Lemma D.41(iv) is applied gate by gate, so the remark is read per gate (the stronger reading)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.47, p.193; Definition 9.3, p.118; Definition 9.4, p.119; Lemma D.41(iv), p.189

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_GDesc
import Definitions.Def_QuantumKtSoI_Supplement_ExactBlock

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.47** (Gate sets that compile into `G`; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.193). Let `G′` be a finite gate set with an encoding that
satisfies (Enc), such that every gate of `G′` has a real-encoded `G`-block; by Lemma D.41(iv), an exact `G`-block suffices. There is a constant `A₂` such that, for all strings `x, y`,
writing `κ′ = qKt_{G′}(y|x)` and `L = log(|x|+2)`,
`qKt(y|x) ≤ κ′ + L + A₂ log(κ′ + L + 2) + A₂ ≤ κ′ + log(|x|+2) + O(log(κ′+2)) + O(log log(|x|+4))`.

**Formalization Note** `G` is any admissible glue routine set (p.24). The gate set is a `GateLib`
with `Wf`, the encoding satisfies `EncHyp`, blocks are those of Definition 9.4, and `qKt_{G′}` is
`qKtG`. The block hypothesis is stated per gate as "a real-encoded `G`-block or an exact `G`-block", which writes out the remark "an exact `G`-block suffices". The `O(·)` terms are one constant `K` chosen with `A₂`. Logarithms are base 2. -/
theorem theorem_D_47 (G : GlueRoutines) (hG : G.Admissible) (L : GateLib) (hL : L.Wf)
    (enc : {A : GCodedMachine L // A.Valid} → List Bool) (hE : EncHyp L enc)
    (hblk : ∀ g : L.ι, RealBlock nativeLib (L.amp g) ∨ ExactBlock nativeLib (L.amp g)) :
    ∃ A₂ K : ℝ, (∀ x y : List Bool,
      (qKt G y x : ℝ) ≤
          (qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            A₂ * Real.logb 2 ((qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) + 2) + A₂ ∧
        (qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            A₂ * Real.logb 2 ((qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) + 2) + A₂ ≤
          (qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            K * Real.logb 2 ((qKtG L enc G y x : ℝ) + 2) +
            K * Real.logb 2 (Real.logb 2 ((x.length : ℝ) + 4))) := by sorry

end QuantumKtSoI.Supplement
