-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_rename_843ff05dc414
-- name    : P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_rename_843ff05dc414
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:19.559411+00:00
-- url     : https://prove2.me/theorems/23aaf3a0-f680-40e6-904f-f7159d97cc8c
-- title:
--   P2 M Ground Theory Heights  Heights is Weighted Homogeneous rename 843ff05dc414: P2 M Ground Theory Heights  Heights is Weighted Homogeneous rename 843ff05dc414
-- statement:
--   The P2 M Ground Theory Heights  Heights is Weighted Homogeneous rename 843ff05dc414 construction uses the P2 M Ground Theory Heights  Heights is Weighted Homogeneous rename 843ff05dc414 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L175-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L175-L187

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
variable {k n : ℕ}
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_rename_843ff05dc414 {σ τ : Type*} {e : σ → τ} (he : Function.Injective e)
    {w : σ → ℕ} {w' : τ → ℕ} (hw : ∀ x, w' (e x) = w x) {p : MvPolynomial σ R} {a : ℕ}
    (hp : IsWeightedHomogeneous w p a) : IsWeightedHomogeneous w' (rename e p) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isWeightedHomogeneous_rename» := P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_rename_843ff05dc414
