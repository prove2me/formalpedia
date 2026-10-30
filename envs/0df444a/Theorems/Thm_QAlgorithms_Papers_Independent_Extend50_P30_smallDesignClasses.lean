-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_smallDesignClasses
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.smallDesignClasses
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:24:08.352328+00:00
-- url     : https://prove2.me/theorems/0d6831e4-3cf2-4fa9-9729-64de49d9dbfb
-- title:
--   Small permutation-transpose class counts
-- statement:
--   For prime $d$ and $t\geq1$, the class count $M_{t,d}$ is at most $|\Sigma_{t,t}(d)|$. For $d=t=3$, the two classes are represented by the diagonal graph and the all-ones CSS relation. For $d=3,t=4$, the three classes are represented by the diagonal, the anti-identity graph (diagonal entries one and other entries two), and the row space of the explicit matrix printed on PDF p.52. These are permutation-transpose classes, not orthogonal double cosets.
--
--   $$
--   |\Sigma_{3,3}(3)|=8=6+2,\quad M_{3,3}=2;\qquad |\Sigma_{4,4}(3)|=80=24+24+32,\quad M_{4,3}=3.
--   $$
--
--   This gives the source's small permutation-transpose class counts in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 51, remark-6.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF pp.51--52, Remark 6.3: actual representatives and class sizes for both examples. -/
theorem smallDesignClasses :
    (∀ (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)], 1 ≤ t →
      (designClasses d t).card ≤ commutantCount d t) ∧
    Nat.card (Lagrangian 3 3) = 8 ∧ (designClasses 3 3).card = 2 ∧
    (designClassOf (graphRelation (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)))).card = 6 ∧
    (designClassOf (cssRelation qutritDefect)).card = 2 ∧
    designClasses 3 3 = {designClassOf (graphRelation (1 : Matrix (Fin 3) (Fin 3) (ZMod 3))),
      designClassOf (cssRelation qutritDefect)} ∧
    Nat.card (Lagrangian 3 4) = 80 ∧ (designClasses 3 4).card = 3 ∧
    (designClassOf (graphRelation (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)))).card = 24 ∧
    (designClassOf (graphRelation qutritFourAnti)).card = 24 ∧
    (designClassOf qutritFourThird).card = 32 ∧
    designClasses 3 4 = {designClassOf (graphRelation (1 : Matrix (Fin 4) (Fin 4) (ZMod 3))),
      designClassOf (graphRelation qutritFourAnti), designClassOf qutritFourThird} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
