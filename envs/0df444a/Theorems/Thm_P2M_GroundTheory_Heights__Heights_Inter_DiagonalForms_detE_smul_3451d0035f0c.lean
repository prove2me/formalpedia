-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_smul_3451d0035f0c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_smul_3451d0035f0c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:32.594934+00:00
-- url     : https://prove2.me/theorems/d47adf19-4511-4b9d-a7e7-747673018a0e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms det E smul 3451d0035f0c: P2 M Ground Theory Heights  Heights Inter Diagonal Forms det E smul 3451d0035f0c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms det E smul 3451d0035f0c construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms det E smul 3451d0035f0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L136-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
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
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_smul_3451d0035f0c (e : Module.Basis (Fin 2) Ω E) (α β : Ω) (u w : E) :
    T.detE e (α • u) (β • w) = α * β * T.detE e u w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«detE_smul» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_smul_3451d0035f0c
