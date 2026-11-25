-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_nsmul_mem_0148272bd536
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_nsmul_mem_0148272bd536
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:59:15.705075+00:00
-- url     : https://prove2.me/theorems/5b253bca-106f-40c8-99e4-677f15ccecc7
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift exists nsmul mem 0148272bd536: P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift exists nsmul mem 0148272bd536
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift exists nsmul mem 0148272bd536 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift exists nsmul mem 0148272bd536 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCongruenceLift.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCongruenceLift.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsNsmulMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.CongruenceLift

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_nsmul_mem_0148272bd536 {E W : Type*} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) : ∃ d : ℕ, 0 < d ∧ d • w ∈ La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«CongruenceLift».«exists_nsmul_mem» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_nsmul_mem_0148272bd536
