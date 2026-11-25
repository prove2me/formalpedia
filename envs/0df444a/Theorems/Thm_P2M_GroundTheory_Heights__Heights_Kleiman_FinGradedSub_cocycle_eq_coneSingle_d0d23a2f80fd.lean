-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cocycle_eq_coneSingle_d0d23a2f80fd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cocycle_eq_coneSingle_d0d23a2f80fd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:20.168577+00:00
-- url     : https://prove2.me/theorems/87183c93-2412-40d6-8161-e43476b5fc16
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cocycle eq cone Single d0d23a2f80fd: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cocycle eq cone Single d0d23a2f80fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cocycle eq cone Single d0d23a2f80fd construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cocycle eq cone Single d0d23a2f80fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L86-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L86-L105

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cocycle_eq_coneSingle_d0d23a2f80fd {c : ℤ} {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) (hK : K.1.1 ⊆ support x) :
    ∃ v ∈ (M.tildeSys c).secs, M.cellCone K.1 (z K) = coneSingle S x c v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«cocycle_eq_coneSingle» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cocycle_eq_coneSingle_d0d23a2f80fd
