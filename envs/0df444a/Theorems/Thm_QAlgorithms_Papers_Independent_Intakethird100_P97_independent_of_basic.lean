-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P97_independent_of_basic
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P97.independent_of_basic
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:43:45.798262+00:00
-- url     : https://prove2.me/theorems/ae5dfc2c-d0ee-4702-b2ef-684864ec8aca
-- title:
--   Section 4, unnumbered: independence from the basic inequalities
-- statement:
--   In the coordinate order $(A,B,C,D,AB,AC,AD,BC,BD,CD,ABC,ABD,ACD,BCD,ABCD)$, define the two formal entropy vectors by
--
--   $$
--   v_1=(3,3,2,2,4,3,3,3,3,4,4,4,3,3,2),\qquad
--   v_2=(3,3,3,3,4,4,4,4,4,6,5,5,5,5,2).
--   $$
--
--   Set the empty coordinate to zero. Mutual information and conditional mutual information of these formal vectors mean the corresponding linear combinations of their coordinates. The basic inequalities mean entropy nonnegativity, Araki–Lieb $S(XY)-S(Y)+S(X)\ge0$, weak monotonicity $S(Z\mid X)+S(Z\mid Y)\ge0$, mutual-information nonnegativity, and conditional-mutual-information nonnegativity, for every disjoint grouping of the four factors (empty groups included). For each $j\in\{1,2\}$ and every $t>0$, the formal vector $h=t v_j$ satisfies
--
--   $$
--    h\text{ satisfies all basic inequalities},\quad I_h(A;C\mid B)=I_h(B;C\mid A)=I_h(A;B\mid D)=0,\quad I_h(C;D)<I_h(C;AB).
--   $$
--
--   These explicit countermodels establish that the constrained conclusion cannot follow from the basic linear inequalities and the three equalities alone.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, PDF p. 6, Section 4, unnumbered

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "A" => ({0} : Finset (Fin 4))

local notation "B" => ({1} : Finset (Fin 4))

local notation "C" => ({2} : Finset (Fin 4))

local notation "D" => ({3} : Finset (Fin 4))

/-- PDF p.6, §4: explicit linear countermodels to derivability from the basic
inequalities. Every positive multiple of either printed ray obeys all basic
inequalities and all three constraints but violates the new inequality. -/
theorem independent_of_basic :
    ∀ h ∈ ({rayOne, rayTwo} : Set (Finset (Fin 4) → ℝ)), ∀ t : ℝ, 0 < t →
      BasicInequalities (fun s => t * h s) ∧ Constraints (fun s => t * h s) ∧
      mutualValue (fun s => t * h s) C D < mutualValue (fun s => t * h s) C (A ∪ B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P97

end
