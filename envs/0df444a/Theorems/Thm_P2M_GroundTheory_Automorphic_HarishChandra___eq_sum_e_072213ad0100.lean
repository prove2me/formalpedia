-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_HarishChandra___eq_sum_e_072213ad0100
-- name    : P2M_GroundTheory_Automorphic_HarishChandra___eq_sum_e_072213ad0100
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:55.469803+00:00
-- url     : https://prove2.me/theorems/6d1fc71d-4763-4519-8a79-0ca8b19c44f8
-- title:
--   P2 M Ground Theory Automorphic Harish Chandra   eq sum e 072213ad0100: P2 M Ground Theory Automorphic Harish Chandra   eq sum e 072213ad0100
-- statement:
--   The P2 M Ground Theory Automorphic Harish Chandra   eq sum e 072213ad0100 construction uses the P2 M Ground Theory Automorphic Harish Chandra   eq sum e 072213ad0100 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L61-L64

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}

theorem P2M_GroundTheory_Automorphic_HarishChandra___eq_sum_e_072213ad0100 (X : gl n) :
    UniversalEnvelopingAlgebra.ι ℂ X = ∑ a : Fin n × Fin n, X a.1 a.2 • e (n := n) a := by sorry

alias «GroundTheory».«Automorphic».«HarishChandra».«ι_eq_sum_e» := P2M_GroundTheory_Automorphic_HarishChandra___eq_sum_e_072213ad0100
