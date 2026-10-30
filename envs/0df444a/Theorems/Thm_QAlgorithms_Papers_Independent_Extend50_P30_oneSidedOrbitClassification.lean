-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_oneSidedOrbitClassification
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.oneSidedOrbitClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:14:05.183035+00:00
-- url     : https://prove2.me/theorems/42f7035c-9b48-47e8-80fe-921ee5aa8527
-- title:
--   Classification of one-sided cosets
-- statement:
--   For prime $d$ and $t\geq1$, the left $O_t(d)$ orbits on $\Sigma_{t,t}(d)$ are classified exactly by the right defect; the right orbits are classified exactly by the left defect. Every defect subspace occurs on either side.
--
--   $$
--   T^\prime\in O_t(d)T\iff T^\prime_{RD}=T_{RD},\qquad T^\prime\in TO_t(d)\iff T^\prime_{LD}=T_{LD}.
--   $$
--
--   This gives the source's classification of one-sided cosets in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 39, remark-4.22

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.39, Remark 4.22: both one-sided classifications and surjectivity onto all defects. -/
theorem oneSidedOrbitClassification (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t) :
    (∀ T S : Lagrangian d t,
      (∃ O : StochasticOrthogonal d t, S.val = actedRelation O.val 1 T.val) ↔
        rightDefect T.val = rightDefect S.val) ∧
    (∀ T S : Lagrangian d t,
      (∃ O : StochasticOrthogonal d t, S.val = actedRelation 1 O.val T.val) ↔
        leftDefect T.val = leftDefect S.val) ∧
    (∀ N : Submodule (ZMod d) (ResidueRegister d t), IsDefect N →
      (∃ T : Lagrangian d t, leftDefect T.val = N) ∧
      (∃ T : Lagrangian d t, rightDefect T.val = N)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
