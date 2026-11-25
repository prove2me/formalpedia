-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_cocycle_9cb775dde1c6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_cocycle_9cb775dde1c6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:25.171598+00:00
-- url     : https://prove2.me/theorems/7d950034-9fca-5fec-abcb-a0c110b801ce
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone cocycle 9cb775dde1c6: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone cocycle 9cb775dde1c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone cocycle 9cb775dde1c6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone cocycle 9cb775dde1c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L29-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L29-L84

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_cocycle_9cb775dde1c6 {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : Cech.d (locSys S N M.coneSub) locResS 0 z = 0)
    (K K' : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0)
    (hK : K.1.1 ⊆ support x) (hK' : K'.1.1 ⊆ support x) :
    M.cellCone K.1 (z K) = M.cellCone K'.1 (z K') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«cellCone_cocycle» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_cocycle_9cb775dde1c6
