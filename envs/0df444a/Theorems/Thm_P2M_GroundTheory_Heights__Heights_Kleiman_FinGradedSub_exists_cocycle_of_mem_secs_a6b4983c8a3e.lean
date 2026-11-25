-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_cocycle_of_mem_secs_a6b4983c8a3e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_cocycle_of_mem_secs_a6b4983c8a3e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:09.869896+00:00
-- url     : https://prove2.me/theorems/ad6fd3b1-735d-41e4-a671-39b7b0e60fbb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub exists cocycle of mem secs a6b4983c8a3e: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub exists cocycle of mem secs a6b4983c8a3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub exists cocycle of mem secs a6b4983c8a3e construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub exists cocycle of mem secs a6b4983c8a3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L107-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L107-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
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
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_cocycle_of_mem_secs_a6b4983c8a3e {c : ℤ} {v : Ω} (hv : v ∈ (M.tildeSys c).secs) :
    ∃ z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0,
      ∀ K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0, K.1.1 ⊆ support x →
        M.cellCone K.1 (z K) = coneSingle S x c v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«exists_cocycle_of_mem_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_cocycle_of_mem_secs_a6b4983c8a3e
