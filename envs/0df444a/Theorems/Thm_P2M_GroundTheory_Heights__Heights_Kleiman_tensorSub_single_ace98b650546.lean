-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_single_ace98b650546
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_single_ace98b650546
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:31.450122+00:00
-- url     : https://prove2.me/theorems/8a3cab0e-1e25-58af-abef-a703dd1f28f9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tensor Sub single ace98b650546: P2 M Ground Theory Heights  Heights Kleiman tensor Sub single ace98b650546
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tensor Sub single ace98b650546 construction uses the P2 M Ground Theory Heights  Heights Kleiman tensor Sub single ace98b650546 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefRestrict.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefRestrict.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_single_ace98b650546 (L : SubSystem S x Ω) (T : Finset (Fin 1)) :
    tensorSub ![L] T = if (0 : Fin 1) ∈ T then L else twistSys S x 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«tensorSub_single» := P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_single_ace98b650546
