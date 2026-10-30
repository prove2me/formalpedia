-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_defectClassification
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.defectClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:09:59.539154+00:00
-- url     : https://prove2.me/theorems/8ebc3465-5b6d-499b-aabe-d3cea735ee3b
-- title:
--   Canonical defect classification
-- statement:
--   Let $d$ be prime, $t\geq1$, and $T\in\Sigma_{t,t}(d)$. Its left and right kernels $N=T_{LD}$ and $M=T_{RD}$ are defect subspaces of the same dimension, and contain the all-ones vector simultaneously. Their dot-product annihilators are the left and right projections of $T$. The relation itself uniquely induces a stochastic quadratic isomorphism $T_J:M^\perp/M\to N^\perp/N$, independent of representative choices, and the defect data reconstruct $T$ exactly.
--
--   $$
--   T=\{(x,y):x\in N^\perp,\ y\in M^\perp,\ [x]=T_J[y]\}.
--   $$
--
--   This gives the source's canonical defect classification in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 37, proposition-4.17

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.37, Proposition 4.17: all six clauses, including the uniquely induced quotient map. -/
theorem defectClassification (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (T : Lagrangian d t) :
    IsDefect (leftDefect T.val) ∧ IsDefect (rightDefect T.val) ∧
    Module.finrank (ZMod d) (leftDefect T.val) = Module.finrank (ZMod d) (rightDefect T.val) ∧
    ((fun _ => 1) ∈ leftDefect T.val ↔ (fun _ => 1) ∈ rightDefect T.val) ∧
    (∀ x, x ∈ perpendicular (leftDefect T.val) ↔ ∃ y, (x, y) ∈ T.val) ∧
    (∀ y, y ∈ perpendicular (rightDefect T.val) ↔ ∃ x, (x, y) ∈ T.val) ∧
    ∃! J : DefectIsomorphism (rightDefect T.val) (leftDefect T.val),
      (∀ q, J.linearEquiv q = canonicalDefectMap T.val q) ∧
      (T.val : Set _) = defectRelationSet (leftDefect T.val) (rightDefect T.val) J ∧
      T.val = defectRelation (leftDefect T.val) (rightDefect T.val) J := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
