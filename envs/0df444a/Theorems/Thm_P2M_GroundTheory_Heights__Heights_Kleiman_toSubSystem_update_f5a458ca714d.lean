-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_toSubSystem_update_f5a458ca714d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_toSubSystem_update_f5a458ca714d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:44.933835+00:00
-- url     : https://prove2.me/theorems/98f4b407-34aa-406d-984f-e025543a7385
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman to Sub System update f5a458ca714d: P2 M Ground Theory Heights  Heights Kleiman to Sub System update f5a458ca714d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman to Sub System update f5a458ca714d construction uses the P2 M Ground Theory Heights  Heights Kleiman to Sub System update f5a458ca714d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L126-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L126-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
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
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_toSubSystem_update_f5a458ca714d {n : ℕ} (L : Fin n → LineBundle k x) (i : Fin n) (Y : LineBundle k x) :
    (fun j => (Function.update L i Y j).toSubSystem) =
      Function.update (fun j => (L j).toSubSystem) i Y.toSubSystem := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«toSubSystem_update» := P2M_GroundTheory_Heights__Heights_Kleiman_toSubSystem_update_f5a458ca714d
