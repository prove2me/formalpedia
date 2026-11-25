-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_1768146d2888
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_1768146d2888
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:57.368116+00:00
-- url     : https://prove2.me/theorems/82178ea9-bce1-4122-980f-a5ba87248833
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift zcoeff   pow 1768146d2888: P2 M Ground Theory PAdic Hodge Teich Lift zcoeff   pow 1768146d2888
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift zcoeff   pow 1768146d2888 construction uses the P2 M Ground Theory PAdic Hodge Teich Lift zcoeff   pow 1768146d2888 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L570-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L570-L571

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}

theorem P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_1768146d2888 (N : ℕ) : T.zcoeff (T.π ^ N) = Pi.single (N : ℤ) 1 := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«zcoeff_π_pow» := P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_1768146d2888
