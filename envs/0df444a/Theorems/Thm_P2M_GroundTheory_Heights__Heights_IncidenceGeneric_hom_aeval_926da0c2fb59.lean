-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hom_aeval_926da0c2fb59
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hom_aeval_926da0c2fb59
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:24:37.858831+00:00
-- url     : https://prove2.me/theorems/d10aef62-e134-41c0-8749-bf5391845635
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Generic hom aeval 926da0c2fb59: P2 M Ground Theory Heights  Heights Incidence Generic hom aeval 926da0c2fb59
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Generic hom aeval 926da0c2fb59 construction uses the P2 M Ground Theory Heights  Heights Incidence Generic hom aeval 926da0c2fb59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L13-L19

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

theorem P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hom_aeval_926da0c2fb59 {F σ R T : Type*} [Field F] [CommRing R] [CommRing T] [Algebra F R] [Algebra F T]
    (Φ : R →+* T) (hΦ : ∀ r : F, Φ (algebraMap F R r) = algebraMap F T r) (y : σ → R)
    (g : MvPolynomial σ F) : Φ (aeval y g) = aeval (fun s => Φ (y s)) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceGeneric».«hom_aeval» := P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hom_aeval_926da0c2fb59
