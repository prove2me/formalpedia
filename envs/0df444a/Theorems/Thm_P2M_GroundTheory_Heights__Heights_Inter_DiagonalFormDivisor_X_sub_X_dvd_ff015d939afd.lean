-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_X_sub_X_dvd_ff015d939afd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_X_sub_X_dvd_ff015d939afd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:30.886801+00:00
-- url     : https://prove2.me/theorems/3a65022f-70cf-4f0d-9d94-1e1e60d7ac88
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor X sub X dvd ff015d939afd: P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor X sub X dvd ff015d939afd
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor X sub X dvd ff015d939afd construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Form Divisor X sub X dvd ff015d939afd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L110-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean#L110-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_X_sub_X_dvd_ff015d939afd {R : Type} [CommRing R] (P : MvPolynomial (Fin 2) R) :
    (X 1 - X 0 : MvPolynomial (Fin 2) R) ∣ P - aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalFormDivisor».«X_sub_X_dvd» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_X_sub_X_dvd_ff015d939afd
