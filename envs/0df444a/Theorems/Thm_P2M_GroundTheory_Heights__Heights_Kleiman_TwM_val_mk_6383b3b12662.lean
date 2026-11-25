-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwM_val_mk_6383b3b12662
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwM_val_mk_6383b3b12662
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:34.849565+00:00
-- url     : https://prove2.me/theorems/6008e5ef-eaa8-50e1-bba2-fb17c9cb70b4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Tw M val mk 6383b3b12662: P2 M Ground Theory Heights  Heights Kleiman Tw M val mk 6383b3b12662
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Tw M val mk 6383b3b12662 construction uses the P2 M Ground Theory Heights  Heights Kleiman Tw M val mk 6383b3b12662 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitObj.lean#L289-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitObj.lean#L289-L290

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) {r : ℕ} (η : Fin (r + 1) → Ω)
variable {x}
variable {η}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwM_val_mk_6383b3b12662 {M₀ : FinGradedSub (S := S) (x := x) Ω} (v : LaurUT Ω) (hv : IsTw η M₀ v) :
    (TwM.mk v hv).val = v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwM».«val_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_TwM_val_mk_6383b3b12662
