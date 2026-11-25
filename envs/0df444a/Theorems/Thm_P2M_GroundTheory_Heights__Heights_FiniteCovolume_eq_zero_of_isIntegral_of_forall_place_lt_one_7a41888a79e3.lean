-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_isIntegral_of_forall_place_lt_one_7a41888a79e3
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_isIntegral_of_forall_place_lt_one_7a41888a79e3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:42:24.266703+00:00
-- url     : https://prove2.me/theorems/4c820665-e5d9-40bf-bb7a-f7c8a7646187
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume eq zero of is Integral of forall place lt one 7a41888a79e3: P2 M Ground Theory Heights  Heights Finite Covolume eq zero of is Integral of forall pla
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume eq zero of is Integral of forall place lt one 7a41888a79e3 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume eq zero of is Integral of forall place lt one 7a41888a79e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchLatticeDiscrete.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchLatticeDiscrete.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_isIntegral_of_forall_place_lt_one_7a41888a79e3 {K : Type*} [Field K] [NumberField K] {c : K}
    (hc : IsIntegral ℤ c) (hlt : ∀ w : InfinitePlace K, w c < 1) : c = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«eq_zero_of_isIntegral_of_forall_place_lt_one» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_isIntegral_of_forall_place_lt_one_7a41888a79e3
