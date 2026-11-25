-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMod_quot_eq_zero_1dfdbf1c2e89
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locMod_quot_eq_zero_1dfdbf1c2e89
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:47.954914+00:00
-- url     : https://prove2.me/theorems/90fdc42e-c9d8-4a01-80ea-40b3b145af83
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Mod quot eq zero 1dfdbf1c2e89: P2 M Ground Theory Heights  Heights Kleiman loc Mod quot eq zero 1dfdbf1c2e89
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Mod quot eq zero 1dfdbf1c2e89 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Mod quot eq zero 1dfdbf1c2e89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L84-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L84-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locMod_quot_eq_zero_1dfdbf1c2e89 {J : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ J) (hyi : y i = 0)
    (x : LocMod S N (Poly S N ⧸ primeOf (S := S) y) J) : x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locMod_quot_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_locMod_quot_eq_zero_1dfdbf1c2e89
