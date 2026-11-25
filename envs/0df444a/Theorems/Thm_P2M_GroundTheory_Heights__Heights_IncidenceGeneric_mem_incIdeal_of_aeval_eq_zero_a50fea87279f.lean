-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_mem_incIdeal_of_aeval_eq_zero_a50fea87279f
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceGeneric_mem_incIdeal_of_aeval_eq_zero_a50fea87279f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:07.121953+00:00
-- url     : https://prove2.me/theorems/52ef4187-bea8-516a-ad65-80f15226335d
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Generic mem inc Ideal of aeval eq zero a50fea87279f: P2 M Ground Theory Heights  Heights Incidence Generic mem inc Ideal of aeval eq zero a50fea87279f
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Generic mem inc Ideal of aeval eq zero a50fea87279f construction uses the P2 M Ground Theory Heights  Heights Incidence Generic mem inc Ideal of aeval eq zero a50fea87279f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L47-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncidenceGeneric.lean#L47-L121

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

theorem P2M_GroundTheory_Heights__Heights_IncidenceGeneric_mem_incIdeal_of_aeval_eq_zero_a50fea87279f {F : Type*} [Field F] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ P)))
    (g : MvPolynomial (Fin k × Fin n) F) (h : aeval (genSubst (genPt P) c) g = 0) :
    g ∈ incIdeal P k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceGeneric».«mem_incIdeal_of_aeval_eq_zero» := P2M_GroundTheory_Heights__Heights_IncidenceGeneric_mem_incIdeal_of_aeval_eq_zero_a50fea87279f
