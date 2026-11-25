-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_secs_le_of_surjective_f10808922dce
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_secs_le_of_surjective_f10808922dce
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:44.076913+00:00
-- url     : https://prove2.me/theorems/d3ec3e79-4df8-4772-a555-b7f88cf1760f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman secs le of surjective f10808922dce: P2 M Ground Theory Heights  Heights Kleiman secs le of surjective f10808922dce
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman secs le of surjective f10808922dce construction uses the P2 M Ground Theory Heights  Heights Kleiman secs le of surjective f10808922dce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L120-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L120-L220

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_secs_le_of_surjective_f10808922dce (hy : y ≠ 0) (n : ℕ)
    (hsurj : Function.Surjective (toH0 (primeQuotGraded (S := S) y) (n : ℤ))) :
    (twistSys S y (n : ℤ)).secs ≤ (coordGraded S y).piece (n : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«secs_le_of_surjective» := P2M_GroundTheory_Heights__Heights_Kleiman_secs_le_of_surjective_f10808922dce
