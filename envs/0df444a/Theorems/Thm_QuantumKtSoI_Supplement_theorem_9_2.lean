-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_9_2
-- name    : QuantumKtSoI.Supplement.theorem_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:48:20.924802+00:00
-- url     : https://prove2.me/theorems/db357d8b-787b-436c-8472-297e810c1ac1
-- title:
--   Theorem 9.2, p.118 — for every polynomially universal machine $U$, infinitely many pairs have $\mathrm{qKt}_U$-defect above $B(\log(|x|+|y|+2))^a$
-- statement:
--   Let $U$ be a machine and
--   $$\mathrm{qKt}_U(y|x)=\min_{p,t}\{|p|+\lceil\log t\rceil : P_U(\langle p,x\rangle;t,y)\ge 2/3\}$$
--   the measure defined by its programs. Suppose that $U$ is polynomially universal, that is, satisfies Equation (23): there are positive integers $k_U,C_U,d_U$ and for every description $e$ a program $p_e$ with $|p_e|\le|e|+k_U$ and $P_U(\langle p_e,x\rangle;C_U(t+|e|+|x|+1)^{d_U},y)\ge P_e(x;t,y)$ for all $x,y$ and $t\ge1$. Then for every integer $a\ge1$ and every real $B>0$, infinitely many pairs $(x,y)$ satisfy
--   $$\mathrm{qKt}_U(x)+\mathrm{qKt}_U(y|x)-\mathrm{qKt}_U(\langle x,y\rangle)>B(\log(|x|+|y|+2))^a .$$
--
--   So the worst-case failure with every polylogarithmic error does not depend on the description language, only on polynomial universality.
--
--   **Formalization Note** Logarithms are base $2$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - encoding: qKt_U(x) + qKt_U(y|x) − qKt_U(⟨x,y⟩) > B(log(|x|+|y|+2))^a with qKt_U possibly +∞ by definition → qKt_U is ℕ∞-valued and the inequality is written without subtraction in [0,∞]: qKt_U(⟨x,y⟩) + B(log(…))^a < qKt_U(x) + qKt_U(y|x); reason: the same inequality when the three values are finite, which they are under Equation (23) (p.118)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 9.2, p.118; qKt_U and Equation (23), pp.117–118

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_qKtU

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 9.2** (Worst-case failure for universal machines; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.118). Suppose that the fixed
machine `U` is polynomially universal, that is, satisfies Equation (23). For every integer `a ≥ 1`
and every real `B > 0`, infinitely many pairs `(x, y)` satisfy
`qKt_U(x) + qKt_U(y|x) − qKt_U(⟨x,y⟩) > B(log(|x|+|y|+2))^a`.

**Formalization Note** `qKt_U` takes values in `ℕ∞` (`+∞` on an empty feasible set, p.117);
under Equation (23) it is finite (p.118). The inequality is written without subtraction,
`qKt_U(⟨x,y⟩) + B(log(|x|+|y|+2))^a < qKt_U(x) + qKt_U(y|x)`, in `ℝ≥0∞`, which is the paper's
inequality whenever the three values are finite. Equation (23) has positive integer constants
`k_U, C_U, d_U` (`PolyUniversal`); the descriptions `e` and `P_e` are those of the admissible glue
routine set `G` (p.24). -/
theorem theorem_9_2 (G : GlueRoutines) (hG : G.Admissible) (U : CodedMachine)
    (hU : ∃ kU CU dU : ℕ, 0 < kU ∧ 0 < CU ∧ 0 < dU ∧ PolyUniversal G U kU CU dU) :
    ∀ a : ℕ, 1 ≤ a → ∀ B : ℝ, 0 < B →
      {p : List Bool × List Bool |
        ((qKtU U (pair p.1 p.2) [] : ENNReal) +
            ENNReal.ofReal (B * Real.logb 2 ((p.1.length : ℝ) + p.2.length + 2) ^ a)) <
          (qKtU U p.1 [] : ENNReal) + (qKtU U p.2 p.1 : ENNReal)}.Infinite := by sorry

end QuantumKtSoI.Supplement
