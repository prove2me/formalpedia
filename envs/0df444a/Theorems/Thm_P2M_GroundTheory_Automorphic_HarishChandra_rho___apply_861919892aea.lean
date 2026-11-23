-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_HarishChandra_rho___apply_861919892aea
-- name    : P2M_GroundTheory_Automorphic_HarishChandra_rho___apply_861919892aea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:14.048141+00:00
-- url     : https://prove2.me/theorems/d213e48c-61ef-414c-97dc-532b761466fc
-- title:
--   P2 M Ground Theory Automorphic Harish Chandra rho   apply 861919892aea: P2 M Ground Theory Automorphic Harish Chandra rho   apply 861919892aea
-- statement:
--   The P2 M Ground Theory Automorphic Harish Chandra rho   apply 861919892aea construction uses the P2 M Ground Theory Automorphic Harish Chandra rho   apply 861919892aea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L64-L66

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
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
open MvPolynomial
variable {n : ℕ}

theorem P2M_GroundTheory_Automorphic_HarishChandra_rho___apply_861919892aea (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) (f : Poly n) :
    rho c (UniversalEnvelopingAlgebra.ι ℂ M) f = rhoDeriv c M f := by sorry

alias «GroundTheory».«Automorphic».«HarishChandra».«rho_ι_apply» := P2M_GroundTheory_Automorphic_HarishChandra_rho___apply_861919892aea
