-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_idealMod_0664d1e72b9b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_idealMod_0664d1e72b9b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:04:54.474331+00:00
-- url     : https://prove2.me/theorems/a389f08f-7903-5778-a40c-90f114f72e07
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Mod le ideal Mod 0664d1e72b9b: P2 M Ground Theory Heights  Heights Kleiman ideal Mod le ideal Mod 0664d1e72b9b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Mod le ideal Mod 0664d1e72b9b construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Mod le ideal Mod 0664d1e72b9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L31-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer
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
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_idealMod_0664d1e72b9b {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    idealMod (x := x) J I ≤ idealMod (x := x) J' I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealMod_le_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_idealMod_0664d1e72b9b
