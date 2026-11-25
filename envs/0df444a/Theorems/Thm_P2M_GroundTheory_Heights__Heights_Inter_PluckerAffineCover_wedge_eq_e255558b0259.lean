-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wedge_eq_e255558b0259
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wedge_eq_e255558b0259
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:13.514292+00:00
-- url     : https://prove2.me/theorems/cd7a25bc-a0c8-4fe2-ad93-f88cbedc5a3b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover wedge eq e255558b0259: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover wedge eq e255558b0259
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover wedge eq e255558b0259 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover wedge eq e255558b0259 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L19-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
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
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wedge_eq_e255558b0259 (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω) (u w : E) :
    ψ u * ψ' w - ψ w * ψ' u = (ψ (e 0) * ψ' (e 1) - ψ (e 1) * ψ' (e 0)) * T.detE e u w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«wedge_eq» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wedge_eq_e255558b0259
