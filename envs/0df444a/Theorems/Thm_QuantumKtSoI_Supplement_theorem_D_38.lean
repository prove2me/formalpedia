-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_38
-- name    : QuantumKtSoI.Supplement.theorem_D_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:53:31.554285+00:00
-- url     : https://prove2.me/theorems/9b119c78-e601-468e-a297-3abf80e3945c
-- title:
--   Theorem D.38, p.184 — the symmetry failures hold for $\mathrm{qKt}_U$ for every quasi-linear universal $U$
-- statement:
--   Let $U$ be quasi-linear universal. Then Theorems 5.10, 5.16 and 5.22, Corollaries 5.13 and 5.24, and parts (ii) and (iii) of Corollary 5.15 hold with $\mathrm{qKt}_U$ in place of $\mathrm{qKt}$, with the same scales and the same polynomial $p(n)=8000n^2$. That is:
--
--   1. for every real $a\ge1$, infinitely many pairs have $\mathrm{qKt}_U(y|x)-\mathrm{qKt}_U(\langle x,y\rangle)+\mathrm{qKt}_U(x)>2^{(\log\log(|x|+|y|+4))^a}$, and infinitely many $n$ admit such $x,y\in\{0,1\}^n$ with the bound $2^{(\log\log(2n+4))^a}$;
--   2. the same with the iterated clocks $F^{[j]}_a(|x|+|y|)$ and $F^{[j]}_a(2n)$ for all integers $j,a\ge1$;
--   3. for every $C\ge1$ a quantum polynomial-time sampler outputs, for infinitely many $n$ and with probability above $1/(8000n^2)$, a pair of $n$-bit strings with $\mathrm{qKt}_U(y|x)>\mathrm{qKt}_U(\langle x,y\rangle)-\mathrm{qKt}_U(x)+C\log(|x|+|y|+2)$, with the output shape of Theorem 5.16;
--   4. the conditional failures of Theorem 5.22 and Corollary 5.24 with a linear error at every logarithmic weight $\kappa$.
--
--   The sampler, the integer $\beta$ and the slope may depend on $U$; the polynomial $p(n)=8000n^2$ does not.
--
--   So both the worst-case and the average-case symmetry failures hold for every quasi-linear universal machine.
--
--   **Formalization Note** Each restated result is the measure-parameterized statement of the module `SoIFailures`.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - encoding: qKt_U, with the minimum of the empty set equal to +∞ → qKt_U is ℕ∞-valued; the statement first asserts that it is finite everywhere and then reads its values as reals; reason: the restated results are inequalities between finite values; finiteness holds for every polynomially universal machine (p.118)
--   - reading: the sentences on which constants the sampler, β and the slope for qKt_U are built from (C′ ≥ C + k′ + A′, weight κ + 3B_U + 1), and the closing remark on U_ql → the restated results with their own existential constants, quantified after U; reason: these sentences describe how the witnesses are obtained and say they may depend on U; a witness of an existence theorem is not a fixed object
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.38, p.184; Definition 9.1, p.117

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_qKtU
import Definitions.Def_QuantumKtSoI_Supplement_SoIFailures

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.38** (The symmetry failures for quasi-linear universal machines; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.184). Let `U`
be quasi-linear universal. Then Theorems 5.10, 5.16 and 5.22, Corollaries 5.13 and 5.24, and parts
(ii) and (iii) of Corollary 5.15 hold with `qKt_U` in place of `qKt`, with the same scales and the
same polynomial `p(n) = 8000n²`. The sampler and the slope may depend on `U`; `p(n) = 8000n²` does
not.

**Formalization Note** `SoIFailures µ` is the conjunction of the seven restated results for a
real-valued conditional measure `µ` (module `SoIFailures`; at `µ = qKt` each conjunct is the
paper's statement). `qKt_U` is `ℕ∞`-valued (p.117); the statement first asserts that it is finite
(as it is for every polynomially universal machine, p.118, and `U` is one by Theorem D.34), and
then reads its values in `ℝ`. The paper's remarks on which constants the sampler for `qKt_U` is
built from, and its closing sentence about `U_ql`, describe the proof and are not part of the
statement. The descriptions of the restated results are those of the admissible glue routine set
`G` (p.24). -/
theorem theorem_D_38 (G : GlueRoutines) (hG : G.Admissible) (U : CodedMachine)
    (hU : QuasiLinUniversal U) :
    (∀ y x : List Bool, qKtU U y x ≠ ⊤) ∧
      SoIFailures fun y x => ((qKtU U y x).toNat : ℝ) := by sorry

end QuantumKtSoI.Supplement
