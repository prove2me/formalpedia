-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_X_mem_ker_iff_e50bcbd76c39
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_X_mem_ker_iff_e50bcbd76c39
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:18.862251+00:00
-- url     : https://prove2.me/theorems/50ab763f-4ed2-4d44-a329-078fb960eb7c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Relevant X mem ker iff e50bcbd76c39: P2 M Ground Theory Heights  Heights Inter Diagonal Relevant X mem ker iff e50bcbd76c39
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Relevant X mem ker iff e50bcbd76c39 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Relevant X mem ker iff e50bcbd76c39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagRelevant.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagRelevant.lean#L14-L20

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_X_mem_ker_iff_e50bcbd76c39 {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ)
    (p : Σ k, ι k) :
    (X p : MvPolynomial (Σ k, ι k) ℤ) ∈ RingHom.ker (T.multiConeMap c) ↔ c p = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalRelevant».«X_mem_ker_iff» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_X_mem_ker_iff_e50bcbd76c39
