-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistPowsBundle_toSubSystem_1b4b14537e0e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistPowsBundle_toSubSystem_1b4b14537e0e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:40:51.097869+00:00
-- url     : https://prove2.me/theorems/394fa091-430c-5d90-affd-f1f36ab384d7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Pows Bundle to Sub System 1b4b14537e0e: P2 M Ground Theory Heights  Heights Kleiman twist Pows Bundle to Sub System 1b4b14537e0e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Pows Bundle to Sub System 1b4b14537e0e construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Pows Bundle to Sub System 1b4b14537e0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L36-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
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
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistPowsBundle_toSubSystem_1b4b14537e0e (F : LineBundle S x) :
    ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      (twistPowsBundle F t L n).toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistPowsBundle_toSubSystem» := P2M_GroundTheory_Heights__Heights_Kleiman_twistPowsBundle_toSubSystem_1b4b14537e0e
