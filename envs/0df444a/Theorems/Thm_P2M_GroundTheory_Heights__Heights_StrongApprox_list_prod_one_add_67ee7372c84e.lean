-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_list_prod_one_add_67ee7372c84e
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_list_prod_one_add_67ee7372c84e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:31.09167+00:00
-- url     : https://prove2.me/theorems/777db0bd-fdb9-4c55-9784-7dfa8f65e2d8
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx list prod one add 67ee7372c84e: P2 M Ground Theory Heights  Heights Strong Approx list prod one add 67ee7372c84e
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx list prod one add 67ee7372c84e construction uses the P2 M Ground Theory Heights  Heights Strong Approx list prod one add 67ee7372c84e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L100-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L100-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_list_prod_one_add_67ee7372c84e {ι R : Type*} [Ring R] (B : ι → R) (hB : ∀ v w, v ≠ w → B v * B w = 0)
    (l : List ι) (hl : l.Nodup) : (l.map fun v => 1 + B v).prod = 1 + (l.map B).sum := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«list_prod_one_add» := P2M_GroundTheory_Heights__Heights_StrongApprox_list_prod_one_add_67ee7372c84e
