-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_weightSet_nonempty_9935efbea46e
-- name    : P2M_GroundTheory_Heights__Heights_weightSet_nonempty_9935efbea46e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:22.526441+00:00
-- url     : https://prove2.me/theorems/ce130c88-a016-4606-bb22-aac630a7b955
-- title:
--   P2 M Ground Theory Heights  Heights weight Set nonempty 9935efbea46e: P2 M Ground Theory Heights  Heights weight Set nonempty 9935efbea46e
-- statement:
--   The P2 M Ground Theory Heights  Heights weight Set nonempty 9935efbea46e construction uses the P2 M Ground Theory Heights  Heights weight Set nonempty 9935efbea46e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L98-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
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
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}

theorem P2M_GroundTheory_Heights__Heights_weightSet_nonempty_9935efbea46e {p : MvPolynomial σ R} (hp : p ≠ 0) : (weightSet w p).Nonempty := by sorry

alias «GroundTheory».«Heights₂».«Heights».«weightSet_nonempty» := P2M_GroundTheory_Heights__Heights_weightSet_nonempty_9935efbea46e
