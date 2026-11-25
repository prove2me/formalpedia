-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_recR_congr_3c6ea09343e1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_recR_congr_3c6ea09343e1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:43.53183+00:00
-- url     : https://prove2.me/theorems/d8250341-bf95-547e-ab5c-b61c407d2ccd
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IUnique rec R congr 3c6ea09343e1: P2 M Ground Theory Heights  Heights Inter Thm IUnique rec R congr 3c6ea09343e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IUnique rec R congr 3c6ea09343e1 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IUnique rec R congr 3c6ea09343e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L17-L27

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_recR_congr_3c6ea09343e1 {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (h : ∀ W ∈ divSupp P s, IsHorizontal W → I W n L = J W n L) :
    recR I P L A s = recR J P L A s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIUnique».«recR_congr» := P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_recR_congr_3c6ea09343e1
