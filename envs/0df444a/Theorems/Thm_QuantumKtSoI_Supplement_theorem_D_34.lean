-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_34
-- name    : QuantumKtSoI.Supplement.theorem_D_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:52:42.100811+00:00
-- url     : https://prove2.me/theorems/d86d1294-b7c0-4bca-8a2e-3bc1d380a43e
-- title:
--   Theorem D.34, p.183 — $\mathrm{qKt}_U\le\mathrm{qKt}+\log(|x|+2)+A_f\log(\cdots)+A_f$ for quasi-linear universal $U$, which is polynomially universal
-- statement:
--   Let $U$ be quasi-linear universal (Definition 9.1). There is a constant $A_f$ such that, for all strings $x,y$, writing $\kappa=\mathrm{qKt}(y|x)$,
--   $$\mathrm{qKt}_U(y|x)\le\kappa+\log(|x|+2)+A_f\log(\kappa+\log(|x|+2)+2)+A_f .$$
--   Moreover $U$ is polynomially universal in the sense of Equation (23), with $p_e=\overline{\ulcorner I\urcorner}\,e$, where $I$ is the machine of Theorem D.30.
--
--   This is the forward comparison between the description measure and the program measure of a quasi-linear universal machine.
--
--   **Formalization Note** Equation (23) is written out with $p_e=\overline{\ulcorner I\urcorner}\,e$ (the self-delimiting code of the published encoding of $I$, followed by the bit string of $e$) and positive integers $k_U,C_U,d_U$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - generalization: I is the machine of Theorem D.30 → the Moreover clause is stated for every machine I and polynomial p_I with the Theorem D.30 property; reason: the clause follows from condition (U-a) applied to M = I and the D.30 inequality alone; the paper's I has the property
--   - encoding: qKt_U(y|x) ≤ … with qKt_U possibly +∞ by definition → the inequality is stated in [0,∞], so it also asserts that qKt_U(y|x) is finite; reason: qKt_U is ℕ∞-valued (p.117)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.34, p.183; Definition 9.1, p.117; Equation (23), p.118; Theorem D.30, p.181

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_qKtU

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.34** (Forward comparison; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.183). Let `U` be quasi-linear universal. There is a
constant `A_f` such that, for all strings `x, y`, writing `κ = qKt(y|x)`,
`qKt_U(y|x) ≤ κ + log(|x|+2) + A_f log(κ + log(|x|+2) + 2) + A_f`. Moreover `U` is polynomially
universal in the sense of Equation (23), with `p_e = ⌜I⌝‾e`.

**Formalization Note** `I` is "the machine of Theorem D.30"; the Moreover clause is stated for
every machine `I` and polynomial `p_I` with the Theorem D.30 property (`InterpreterProp`), which
contains the paper's `I`. `⌜I⌝‾e` is the self-delimiting code (`sd`, §2.1) of the published encoding of `I` followed by the bit string of `e`;
Equation (23) is written out with this `p_e` and positive integers `k_U, C_U, d_U`. The first
inequality is in `ℝ≥0∞` (`qKt_U` is `ℕ∞`-valued, p.117), so it also asserts that `qKt_U(y|x)` is
finite. `G` is any admissible glue routine set (p.24). -/
theorem theorem_D_34 (G : GlueRoutines) (hG : G.Admissible) (U : CodedMachine)
    (hU : QuasiLinUniversal U) :
    (∃ Af : ℝ, ∀ x y : List Bool,
      (qKtU U y x : ENNReal) ≤
        ENNReal.ofReal ((qKt G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) +
          Af * Real.logb 2 ((qKt G y x : ℝ) + Real.logb 2 ((x.length : ℝ) + 2) + 2) + Af)) ∧
    ∀ I : CodedMachine, ∀ pI : Polynomial ℝ, InterpreterProp G I pI →
      ∃ kU CU dU : ℕ, 0 < kU ∧ 0 < CU ∧ 0 < dU ∧ ∀ e : Desc,
        (sd I.encode ++ e.bits).length ≤ e.bits.length + kU ∧
          ∀ x y : List Bool, ∀ t : ℕ, 1 ≤ t →
            e.prob G x t y ≤ U.toMachine.outputProb (pair (sd I.encode ++ e.bits) x)
              (CU * (t + e.bits.length + x.length + 1) ^ dU) y := by sorry

end QuantumKtSoI.Supplement
