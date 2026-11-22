-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_5_10
-- name    : QuantumKtSoI.Supplement.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:41:37.289034+00:00
-- url     : https://prove2.me/theorems/30745271-a75c-4230-8af8-582acecbd098
-- title:
--   Theorem 5.10, p.59 — infinitely many pairs have symmetry defect above $2^{(\log\log(|x|+|y|+4))^a}$
-- statement:
--   For every real $a\ge1$, infinitely many pairs of strings $(x,y)$ satisfy
--   $$\mathrm{qKt}(y|x)-\mathrm{qKt}(\langle x,y\rangle)+\mathrm{qKt}(x)>2^{(\log\log(|x|+|y|+4))^a}.$$
--   In particular symmetry of information fails with every fixed polylogarithmic error: for all reals $C,k$ some pair has $\mathrm{qKt}(y|x)-\mathrm{qKt}(\langle x,y\rangle)+\mathrm{qKt}(x)>C(\log(|x|+|y|+2))^k$.
--
--   This is the unconditional worst-case failure of symmetry of information for quantum Kt complexity.
--
--   **Formalization Note** The values of $\mathrm{qKt}$ are read in $\mathbb R$ and logarithms are base $2$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - reading: "In particular symmetry fails with every fixed polylogarithmic error" → second conjunct: for all reals C, k some pair has defect > C(log(|x|+|y|+2))^k; reason: writes the informal clause out; symmetry with error θ is a bound for all pairs (Definition 5.3)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 5.10, p.59

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 5.10** (Unconditional failure of symmetry of information; restatement of Theorem 1.3;
Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.59). For every real `a ≥ 1`, infinitely many pairs `(x, y)` satisfy
`qKt(y|x) − qKt(⟨x,y⟩) + qKt(x) > 2^{(log log(|x|+|y|+4))^a}`. In particular symmetry fails with
every fixed polylogarithmic error: for all reals `C, k` some pair has
`qKt(y|x) − qKt(⟨x,y⟩) + qKt(x) > C (log(|x|+|y|+2))^k`.

**Formalization Note** `G` is any admissible glue routine set (p.24). The "in particular" clause
is written out as the second conjunct. Logarithms are base 2; the values of `qKt` are read in
`ℝ`. -/
theorem theorem_5_10 (G : GlueRoutines) (hG : G.Admissible) :
    (∀ a : ℝ, 1 ≤ a →
      {p : List Bool × List Bool |
        (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 ((p.1.length : ℝ) + p.2.length + 4))) ^ a <
          (qKt G p.2 p.1 : ℝ) - qKt G (pair p.1 p.2) [] + qKt G p.1 []}.Infinite) ∧
    ∀ C k : ℝ, ∃ x y : List Bool,
      C * Real.logb 2 ((x.length : ℝ) + y.length + 2) ^ k <
        (qKt G y x : ℝ) - qKt G (pair x y) [] + qKt G x [] := by sorry

end QuantumKtSoI.Supplement
