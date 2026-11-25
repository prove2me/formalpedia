-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locRes_mem_degLoc_397295d09ee9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locRes_mem_degLoc_397295d09ee9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:56.618053+00:00
-- url     : https://prove2.me/theorems/850aeb52-f41a-4fd0-9c38-f4a26f3ac14e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Res mem deg Loc 397295d09ee9: P2 M Ground Theory Heights  Heights Kleiman loc Res mem deg Loc 397295d09ee9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Res mem deg Loc 397295d09ee9 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Res mem deg Loc 397295d09ee9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L34-L42

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
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locRes_mem_degLoc_397295d09ee9 (𝓜 : GradedPMod S N M) (c : ℤ) (I J : StdCell N) (h : I.1 ⊆ J.1)
    {x : LocMod S N M I.1} (hx : x ∈ degLoc 𝓜 c I) : locRes h x ∈ degLoc 𝓜 c J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locRes_mem_degLoc» := P2M_GroundTheory_Heights__Heights_Kleiman_locRes_mem_degLoc_397295d09ee9
