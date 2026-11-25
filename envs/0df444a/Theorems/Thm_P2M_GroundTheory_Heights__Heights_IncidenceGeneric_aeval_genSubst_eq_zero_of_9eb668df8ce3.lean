-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_eq_zero_of_9eb668df8ce3
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_eq_zero_of_9eb668df8ce3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:29.375399+00:00
-- url     : https://prove2.me/theorems/28bf7d16-baa1-5a5e-81d2-8851046380e0
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Generic aeval gen Subst eq zero of 9eb668df8ce3: P2 M Ground Theory Heights  Heights Incidence Generic aeval gen Subst eq zero of 9eb668df8ce3
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Generic aeval gen Subst eq zero of 9eb668df8ce3 construction uses the P2 M Ground Theory Heights  Heights Incidence Generic aeval gen Subst eq zero of 9eb668df8ce3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L38-L45

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

theorem P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_eq_zero_of_9eb668df8ce3 {F R : Type*} [Field F] [CommRing R] [Algebra F R] {n k : ℕ}
    (ζ c c' : Fin n → R) (hc : ∑ l, c l * ζ l = 1) (g : MvPolynomial (Fin k × Fin n) F)
    (h : aeval (genSubst ζ c') g = 0) : aeval (genSubst ζ c) g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceGeneric».«aeval_genSubst_eq_zero_of» := P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_eq_zero_of_9eb668df8ce3
