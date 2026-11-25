-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_of_det_ne_zero_70cc8ca45db3
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_of_det_ne_zero_70cc8ca45db3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:53.691639+00:00
-- url     : https://prove2.me/theorems/09f30d69-15cc-5c2b-bd79-214635ca53b7
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists sheet of det ne zero 70cc8ca45db3: P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists sheet of det ne zero 70cc8ca45d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists sheet of det ne zero 70cc8ca45db3 construction uses the P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists sheet of det ne zero 70cc8ca45db3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L49-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L49-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_sheet_of_det_ne_zero_08ac665d1d09

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_of_det_ne_zero_70cc8ca45db3 {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A *ᵥ s w) (RatChart.ratMap p q x)).det ≠ 0) :
    ∃ s', IsSheetAt J A x s' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetNoChartNull».«exists_sheet_of_det_ne_zero» := P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_of_det_ne_zero_70cc8ca45db3
