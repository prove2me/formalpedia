-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_relComps_of_mem_incidence_6d6a634b74a0
-- name    : P2M_GroundTheory_Heights__Heights_exists_relComps_of_mem_incidence_6d6a634b74a0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:48:05.197117+00:00
-- url     : https://prove2.me/theorems/a56aeb67-f127-55e6-b9dd-947ce8910767
-- title:
--   P2 M Ground Theory Heights  Heights exists rel Comps of mem incidence 6d6a634b74a0: P2 M Ground Theory Heights  Heights exists rel Comps of mem incidence 6d6a634b74a0
-- statement:
--   The P2 M Ground Theory Heights  Heights exists rel Comps of mem incidence 6d6a634b74a0 construction uses the P2 M Ground Theory Heights  Heights exists rel Comps of mem incidence 6d6a634b74a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormReduced.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormReduced.lean#L27-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncIdealSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormReduced
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
variable {F : Type*} [Field F] {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_exists_relComps_of_mem_incidence_6d6a634b74a0 {J : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence J k) :
    ∃ W ∈ relComps J, u ∈ incidence W k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_relComps_of_mem_incidence» := P2M_GroundTheory_Heights__Heights_exists_relComps_of_mem_incidence_6d6a634b74a0
