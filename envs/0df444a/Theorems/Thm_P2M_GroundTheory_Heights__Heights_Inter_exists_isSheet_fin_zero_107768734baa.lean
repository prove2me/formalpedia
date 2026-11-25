-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_isSheet_fin_zero_107768734baa
-- name    : P2M_GroundTheory_Heights__Heights_Inter_exists_isSheet_fin_zero_107768734baa
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:17.784639+00:00
-- url     : https://prove2.me/theorems/9b36c181-3da8-4fdb-9343-e1079e92da2c
-- title:
--   P2 M Ground Theory Heights  Heights Inter exists is Sheet fin zero 107768734baa: P2 M Ground Theory Heights  Heights Inter exists is Sheet fin zero 107768734baa
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter exists is Sheet fin zero 107768734baa construction uses the P2 M Ground Theory Heights  Heights Inter exists is Sheet fin zero 107768734baa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsIsSheetFinZero.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsIsSheetFinZero.lean#L17-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_exists_isSheet_fin_zero_107768734baa {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y) : ∃ γ, IsSheet P Ψ y w γ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«exists_isSheet_fin_zero» := P2M_GroundTheory_Heights__Heights_Inter_exists_isSheet_fin_zero_107768734baa
