-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_55
-- name    : QuantumKtSoI.Supplement.theorem_D_55
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:57:26.479294+00:00
-- url     : https://prove2.me/theorems/507999ff-ccb0-46ac-8b87-08463f41007c
-- title:
--   Theorem D.55, p.198 — $\mathrm{qKt}\le\mathrm{qKt}_{\mathcal G'}+\log(|x|+2)+A_3\log(\cdots)+A_3$ when the gates of $\mathcal G'$ have exact blocks over $\mathcal G\cup\{T\}$
-- statement:
--   Let $\mathcal G'$ be a finite gate set with an encoding that satisfies (Enc), such that every gate of $\mathcal G'$ has an exact $\mathcal G_T$-block, where $\mathcal G_T=\mathcal G\cup\{T\}$ and $T=\mathrm{diag}(1,e^{i\pi/4})$. There is a constant $A_3$ such that, for all strings $x,y$, writing $\kappa'=\mathrm{qKt}_{\mathcal G'}(y|x)$ and $L=\log(|x|+2)$,
--   $$\mathrm{qKt}(y|x)\le\kappa'+L+A_3\log(\kappa'+L+2)+A_3\le\kappa'+\log(|x|+2)+O(\log(\kappa'+2))+O(\log\log(|x|+4)),$$
--   and
--   $$\mathrm{qKt}(y)\le\mathrm{qKt}_{\mathcal G'}(y)+O\big(\log(\mathrm{qKt}_{\mathcal G'}(y)+2)\big).$$
--
--   This gives the reverse comparison for Clifford+$T$ and every gate set that compiles exactly into $\mathcal G\cup\{T\}$.
--
--   **Formalization Note** Logarithms are base $2$ and the values of the measures are read in $\mathbb R$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a finite set G′ of unitary gates with an encoding satisfying (Enc) → a finite indexed family of matrices with a natural-number name per gate (GateLib with Wf: arities ≥ 1, unitary, distinct names), and an injective encoding of the valid coded G′-machines; reason: a finite set with a fixed enumeration of its gate names, which (Enc) presupposes; G′-machines are represented as coded machines as in the base mission
--   - reading: (Enc): a polynomial-time parser recovers the complete finite structural description (no output format fixed) → a deterministic polynomial-time function maps every code to the standard structural record, the published encoding's layout with gate names from the fixed enumeration; reason: the record contains exactly the data Definition 9.3 lists; the paper leaves the format open
--   - reading: O(·) terms in the conclusion → one real constant K, chosen together with the named constant, multiplying each O-term; reason: the usual meaning of O(·) in an upper bound; the terms are at least 1, so one constant serves both
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.55, p.198; Definition 9.3, p.118; Definition 9.4, p.119; G_T, p.195

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_GDesc
import Definitions.Def_QuantumKtSoI_Supplement_ExactBlock

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.55** (Gate sets that compile into `G ∪ {T}`; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.198). Let `G′` be a finite gate set with an encoding that
satisfies (Enc), such that every gate of `G′` has an exact GT-block (a block over `G ∪ {T}`, `T = diag(1, e^{iπ/4})`). There is a constant `A₃` such that, for all strings `x, y`,
writing `κ′ = qKt_{G′}(y|x)` and `L = log(|x|+2)`,
`qKt(y|x) ≤ κ′ + L + A₃ log(κ′ + L + 2) + A₃ ≤ κ′ + log(|x|+2) + O(log(κ′+2)) + O(log log(|x|+4))`, and `qKt(y) ≤ qKt_{G′}(y) + O(log(qKt_{G′}(y) + 2))`.

**Formalization Note** `G` is any admissible glue routine set (p.24). The gate set is a `GateLib`
with `Wf`, the encoding satisfies `EncHyp`, blocks are those of Definition 9.4, and `qKt_{G′}` is
`qKtG`. `nativeT` is the gate set `G ∪ {T}`. The `O(·)` terms are one constant `K` chosen with `A₃`. Logarithms are base 2. -/
theorem theorem_D_55 (G : GlueRoutines) (hG : G.Admissible) (L : GateLib) (hL : L.Wf)
    (enc : {A : GCodedMachine L // A.Valid} → List Bool) (hE : EncHyp L enc)
    (hblk : ∀ g : L.ι, ExactBlock nativeT (L.amp g)) :
    ∃ A₃ K : ℝ, (∀ x y : List Bool,
      (qKt G y x : ℝ) ≤
          (qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            A₃ * Real.logb 2 ((qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) + 2) + A₃ ∧
        (qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            A₃ * Real.logb 2 ((qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) + 2) + A₃ ≤
          (qKtG L enc G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
            K * Real.logb 2 ((qKtG L enc G y x : ℝ) + 2) +
            K * Real.logb 2 (Real.logb 2 ((x.length : ℝ) + 4))) ∧
        ∀ y : List Bool, (qKt G y [] : ℝ) ≤
          (qKtG L enc G y [] : ℝ) + K * Real.logb 2 ((qKtG L enc G y [] : ℝ) + 2) := by sorry

end QuantumKtSoI.Supplement
