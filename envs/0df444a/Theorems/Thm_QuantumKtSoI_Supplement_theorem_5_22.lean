-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_5_22
-- name    : QuantumKtSoI.Supplement.theorem_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:42:41.874254+00:00
-- url     : https://prove2.me/theorems/b78405c2-50a1-48c4-9134-ec923bb4e3cf
-- title:
--   Theorem 5.22, p.71 — conditional symmetry with an auxiliary string fails with linear error at every logarithmic weight
-- statement:
--   For every $\kappa\ge0$ there is $\eta>0$ such that infinitely many triples of strings $(w,x,y)$ satisfy
--   $$\mathrm{qKt}(y|wx)>\mathrm{qKt}(xy|w)-\mathrm{qKt}(x|w)+\eta(|x|+|y|)+\kappa\log(|w|+|x|+|y|+2).$$
--   Here $wx$ and $xy$ are concatenations.
--
--   This is the failure of conditional symmetry of information (Definition 5.17) with a linear error term, for every coefficient of the logarithmic term.
--
--   **Formalization Note** The values of $\mathrm{qKt}$ are read in $\mathbb R$; logarithms are base $2$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 5.22, p.71; Definition 5.17, p.65

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 5.22** (Failure of conditional symmetry of information with an auxiliary string;
Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.71). For every `κ ≥ 0` there is `η > 0` such that infinitely many triples of strings
`(w, x, y)` satisfy `qKt(y|wx) > qKt(xy|w) − qKt(x|w) + η(|x|+|y|) + κ log(|w|+|x|+|y|+2)`.

**Formalization Note** `wx` and `xy` are concatenations, as in the paper; a triple is
`(w, (x, y))`. `G` is any admissible glue routine set (p.24). -/
theorem theorem_5_22 (G : GlueRoutines) (hG : G.Admissible) :
    ∀ κ : ℝ, 0 ≤ κ → ∃ η : ℝ, 0 < η ∧
      {t : List Bool × List Bool × List Bool |
        (qKt G (t.2.1 ++ t.2.2) t.1 : ℝ) - qKt G t.2.1 t.1 +
            η * ((t.2.1.length : ℝ) + t.2.2.length) +
            κ * Real.logb 2 ((t.1.length : ℝ) + t.2.1.length + t.2.2.length + 2) <
          qKt G t.2.2 (t.1 ++ t.2.1)}.Infinite := by sorry

end QuantumKtSoI.Supplement
