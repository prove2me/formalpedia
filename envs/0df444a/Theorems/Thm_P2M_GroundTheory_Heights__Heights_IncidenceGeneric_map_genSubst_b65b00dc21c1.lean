-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_map_genSubst_b65b00dc21c1
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceGeneric_map_genSubst_b65b00dc21c1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:35.188274+00:00
-- url     : https://prove2.me/theorems/8872dd10-11e0-45fe-811a-338df847075b
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Generic map gen Subst b65b00dc21c1: P2 M Ground Theory Heights  Heights Incidence Generic map gen Subst b65b00dc21c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Generic map gen Subst b65b00dc21c1 construction uses the P2 M Ground Theory Heights  Heights Incidence Generic map gen Subst b65b00dc21c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceGeneric

theorem P2M_GroundTheory_Heights__Heights_IncidenceGeneric_map_genSubst_b65b00dc21c1 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n k : ℕ}
    (ζ c : Fin n → R) (ij : Fin k × Fin n) :
    map φ (genSubst ζ c ij) = genSubst (fun l => φ (ζ l)) (fun l => φ (c l)) ij := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceGeneric».«map_genSubst» := P2M_GroundTheory_Heights__Heights_IncidenceGeneric_map_genSubst_b65b00dc21c1
