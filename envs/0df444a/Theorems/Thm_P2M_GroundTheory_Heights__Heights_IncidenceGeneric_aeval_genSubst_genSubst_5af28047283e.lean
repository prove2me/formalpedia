-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_genSubst_5af28047283e
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_genSubst_5af28047283e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:44.015032+00:00
-- url     : https://prove2.me/theorems/eabd6eb5-56eb-4fb2-8080-7884f3ee8800
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Generic aeval gen Subst gen Subst 5af28047283e: P2 M Ground Theory Heights  Heights Incidence Generic aeval gen Subst gen Subst 5af28047283e
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Generic aeval gen Subst gen Subst 5af28047283e construction uses the P2 M Ground Theory Heights  Heights Incidence Generic aeval gen Subst gen Subst 5af28047283e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L26-L36

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

theorem P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_genSubst_5af28047283e {R : Type*} [CommRing R] {n k : ℕ} (ζ c c' : Fin n → R)
    (hc : ∑ l, c l * ζ l = 1) (ij : Fin k × Fin n) :
    aeval (genSubst ζ c) (genSubst ζ c' ij) = genSubst ζ c ij := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceGeneric».«aeval_genSubst_genSubst» := P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_genSubst_5af28047283e
