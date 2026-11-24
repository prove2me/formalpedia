-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_mul__07988fa1a14d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_mul__07988fa1a14d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:03.42271+00:00
-- url     : https://prove2.me/theorems/47c61485-09d9-4414-a8ba-406bf4143fa5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog mul  07988fa1a14d: P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog mul  07988fa1a14d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog mul  07988fa1a14d construction uses the P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog mul  07988fa1a14d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L36-L41

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_mul__07988fa1a14d {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIUnique».«isMultiHomog_mul'» := P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_mul__07988fa1a14d
