-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ker_map_residue_eq_span_e09000dfab17
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ker_map_residue_eq_span_e09000dfab17
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:45.306263+00:00
-- url     : https://prove2.me/theorems/5ade4d42-1650-47d0-8b5b-d43d895d5160
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR ker map residue eq span e09000dfab17: P2 M Ground Theory Heights  Heights Numbers DVR ker map residue eq span e09000dfab17
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR ker map residue eq span e09000dfab17 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR ker map residue eq span e09000dfab17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialIdealCorresp.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialIdealCorresp.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ker_map_residue_eq_span_e09000dfab17 {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type*} :
    RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MvPolynomial σ O →+* _) =
      Ideal.span {C ϖ} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ker_map_residue_eq_span» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ker_map_residue_eq_span_e09000dfab17
