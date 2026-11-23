-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_finSum_succ__591efcd7936f
-- name    : P2M_GroundTheory_PAdicHodge_TeichLift_finSum_succ__591efcd7936f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:03.525808+00:00
-- url     : https://prove2.me/theorems/0ee28942-6c1f-4f89-a2be-717e9c438143
-- title:
--   P2 M Ground Theory PAdic Hodge Teich Lift fin Sum succ  591efcd7936f: P2 M Ground Theory PAdic Hodge Teich Lift fin Sum succ  591efcd7936f
-- statement:
--   The P2 M Ground Theory PAdic Hodge Teich Lift fin Sum succ  591efcd7936f construction uses the P2 M Ground Theory PAdic Hodge Teich Lift fin Sum succ  591efcd7936f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L152-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L152-L158

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
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
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem P2M_GroundTheory_PAdicHodge_TeichLift_finSum_succ__591efcd7936f (a : ℕ → L) (n : ℕ) :
    T.finSum a (n + 1) = T.teich (a 0) + T.π * T.finSum (fun i => a (i + 1)) n := by sorry

alias «GroundTheory».«PAdicHodge».«TeichLift».«finSum_succ'» := P2M_GroundTheory_PAdicHodge_TeichLift_finSum_succ__591efcd7936f
