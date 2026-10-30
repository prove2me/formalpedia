-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_doubleOrbitClassification
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.doubleOrbitClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:13:22.561333+00:00
-- url     : https://prove2.me/theorems/22083925-746b-4552-82ec-117ee2d1015b
-- title:
--   Classification of double cosets
-- statement:
--   For prime $d$, $t\geq1$, and $T,T^\prime\in\Sigma_{t,t}(d)$, membership in the same $O_t(d)$ double coset is equivalent to equality of defect dimension and the all-ones membership invariant. The displayed right defect of $T^\prime$ has the same all-ones membership as its left defect. There are at most $t$ such double cosets.
--
--   $$
--   T^\prime\in O_t(d)TO_t(d)\iff\dim T_{LD}=\dim T^\prime_{LD}\ \text{and}\ (\mathbf1_t\in T_{LD}\iff\mathbf1_t\in T^\prime_{RD}).
--   $$
--
--   This gives the source's classification of double cosets in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 38, corollary-4.21

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.38, Corollary 4.21: complete double-orbit classification and its number bound. -/
theorem doubleOrbitClassification (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t) :
    (∀ T S : Lagrangian d t, SameDoubleOrbit T S ↔
      Module.finrank (ZMod d) (leftDefect T.val) = Module.finrank (ZMod d) (leftDefect S.val) ∧
      ((fun _ => 1) ∈ leftDefect T.val ↔ (fun _ => 1) ∈ rightDefect S.val)) ∧
    (doubleClasses d t).card ≤ t := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
