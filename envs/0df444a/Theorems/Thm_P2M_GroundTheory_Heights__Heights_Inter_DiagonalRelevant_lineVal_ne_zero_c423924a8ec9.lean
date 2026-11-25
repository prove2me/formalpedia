-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_lineVal_ne_zero_c423924a8ec9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_lineVal_ne_zero_c423924a8ec9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:58.56983+00:00
-- url     : https://prove2.me/theorems/4070681b-d5c1-4a11-9c9d-4071588dc398
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Relevant line Val ne zero c423924a8ec9: P2 M Ground Theory Heights  Heights Inter Diagonal Relevant line Val ne zero c423924a8ec9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Relevant line Val ne zero c423924a8ec9 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Relevant line Val ne zero c423924a8ec9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagRelevant.lean#L22-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagRelevant.lean#L22-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagRelevant
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
open GroundTheory.Heights₂.Heights.Inter.DiagonalRelevant

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_lineVal_ne_zero_c423924a8ec9 {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] (e : Module.Basis (Fin 2) Ω E) {ψ : E →ₗ[Ω] Ω} (hψ : ψ ≠ 0) {a : Φ}
    (ha : Transcendental Ω a) : T.lineVal e ψ a ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalRelevant».«lineVal_ne_zero» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_lineVal_ne_zero_c423924a8ec9
