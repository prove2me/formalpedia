-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_congruence_cd72a2a113e6
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_congruence_cd72a2a113e6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:06:25.742922+00:00
-- url     : https://prove2.me/theorems/8aa1a011-209b-481d-bbbf-455fae2af1da
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift exists congruence cd72a2a113e6: P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift exists congruence cd72a2a113e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift exists congruence cd72a2a113e6 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Congruence Lift exists congruence cd72a2a113e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCongruenceLift.lean#L20-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCongruenceLift.lean#L20-L70

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_congruence_cd72a2a113e6 {V G : Type*} [AddCommGroup V] [Group G] [DistribMulAction G V]
    (L : AddSubgroup V) (hL : L.FG) (d : ℕ) (hd : 0 < d) :
    ∃ K : Subgroup (MulAction.stabilizer G L), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ L, ∃ u ∈ L, d • u = (k : G) • y - y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«CongruenceLift».«exists_congruence» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_congruence_cd72a2a113e6
