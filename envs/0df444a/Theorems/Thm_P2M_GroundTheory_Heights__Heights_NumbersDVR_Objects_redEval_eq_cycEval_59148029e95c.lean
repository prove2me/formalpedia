-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_redEval_eq_cycEval_59148029e95c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_redEval_eq_cycEval_59148029e95c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:59.630293+00:00
-- url     : https://prove2.me/theorems/cfb7f856-2a37-4c81-9b99-089260887a49
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Objects red Eval eq cyc Eval 59148029e95c: P2 M Ground Theory Heights  Heights Numbers DVR Objects red Eval eq cyc Eval 59148029e95c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Objects red Eval eq cyc Eval 59148029e95c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Objects red Eval eq cyc Eval 59148029e95c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L95-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_redEval_eq_cycEval_59148029e95c (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (Z : Ideal (MRing ι O) →₀ ℤ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.redEval J Z =
      cycEval (fun W => J (specialIdeal W)) Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Objects».«redEval_eq_cycEval» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_redEval_eq_cycEval_59148029e95c
