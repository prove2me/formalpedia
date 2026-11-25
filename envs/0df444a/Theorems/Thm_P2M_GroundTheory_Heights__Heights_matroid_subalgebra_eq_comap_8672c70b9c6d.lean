-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_matroid_subalgebra_eq_comap_8672c70b9c6d
-- name    : P2M_GroundTheory_Heights__Heights_matroid_subalgebra_eq_comap_8672c70b9c6d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:48:56.989012+00:00
-- url     : https://prove2.me/theorems/0aacd251-01d7-4918-8d80-4225efa25eae
-- title:
--   P2 M Ground Theory Heights  Heights matroid subalgebra eq comap 8672c70b9c6d: P2 M Ground Theory Heights  Heights matroid subalgebra eq comap 8672c70b9c6d
-- statement:
--   The P2 M Ground Theory Heights  Heights matroid subalgebra eq comap 8672c70b9c6d construction uses the P2 M Ground Theory Heights  Heights matroid subalgebra eq comap 8672c70b9c6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTrdegAdjoinLe.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTrdegAdjoinLe.lean#L15-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegAdjoinLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTrdegAdjoinLe
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
open Algebra Cardinal Set AlgebraicIndependent
noncomputable section
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem P2M_GroundTheory_Heights__Heights_matroid_subalgebra_eq_comap_8672c70b9c6d (S : Subalgebra K Ω) :
    AlgebraicIndependent.matroid K S = (AlgebraicIndependent.matroid K Ω).comap ((↑) : S → Ω) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«matroid_subalgebra_eq_comap» := P2M_GroundTheory_Heights__Heights_matroid_subalgebra_eq_comap_8672c70b9c6d
