-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_eq_zero_of_mem_incIdeal_ca256b480e30
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_eq_zero_of_mem_incIdeal_ca256b480e30
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:31.785254+00:00
-- url     : https://prove2.me/theorems/f7da51b3-3317-4d7c-87f8-677b1e4d389b
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Generic aeval eq zero of mem inc Ideal ca256b480e30: P2 M Ground Theory Heights  Heights Incidence Generic aeval eq zero of mem inc Ideal ca256b480e30
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Generic aeval eq zero of mem inc Ideal ca256b480e30 construction uses the P2 M Ground Theory Heights  Heights Incidence Generic aeval eq zero of mem inc Ideal ca256b480e30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L123-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L123-L188

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

theorem P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_eq_zero_of_mem_incIdeal_ca256b480e30 (h₁ : FGNullstellensatz.Statement) {F : Type} [Field F]
    {n k : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)) (hc : ∑ j, c j * genPt P j = 1)
    (g : MvPolynomial (Fin k × Fin n) F) (hg : g ∈ incIdeal P k) :
    aeval (genSubst (genPt P) c) g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceGeneric».«aeval_eq_zero_of_mem_incIdeal» := P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_eq_zero_of_mem_incIdeal_ca256b480e30
