-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_eq_of_lower_0e3246828ea4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_eq_of_lower_0e3246828ea4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:33:50.693688+00:00
-- url     : https://prove2.me/theorems/5f439a5d-6e57-4f48-89a1-b88c81315d32
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IUnique eq of lower 0e3246828ea4: P2 M Ground Theory Heights  Heights Inter Thm IUnique eq of lower 0e3246828ea4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IUnique eq of lower 0e3246828ea4 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IUnique eq of lower 0e3246828ea4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L89-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L89-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIUnique
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_eq_of_lower_0e3246828ea4 {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsRFamily I) (hJ : IsRFamily J) {P : Ideal (MRing ι)} {m : ℕ}
    (L : Fin m → HermLine ι) (A : HermLine ι) (hP : IsArithVar P (m + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hlow : ∀ W, IsArithVar W m → I W m L = J W m L) :
    I P (m + 1) (Fin.snoc L A) = J P (m + 1) (Fin.snoc L A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIUnique».«eq_of_lower» := P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_eq_of_lower_0e3246828ea4
