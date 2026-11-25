-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_cross_mem_b4bbd6c8875a
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_cross_mem_b4bbd6c8875a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:55.639365+00:00
-- url     : https://prove2.me/theorems/b1d5818a-7fa5-4ec7-bcc6-58e34cc431a0
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle cross mem b4bbd6c8875a: P2 M Ground Theory Heights  Heights Section Cycle cross mem b4bbd6c8875a
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle cross mem b4bbd6c8875a construction uses the P2 M Ground Theory Heights  Heights Section Cycle cross mem b4bbd6c8875a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L189-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L189-L199

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_cross_mem_b4bbd6c8875a (hg : D.IsFormSystem d g) {c c' : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (hc' : P.IsLive c') (j j' : Fin (D.size + 1)) :
    X (D.newCoord j) * D.liftOld (chartMonomial c d) * D.liftOld (g c' j') -
      X (D.newCoord j') * D.liftOld (chartMonomial c' d) * D.liftOld (g c j) ∈ D.extIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«cross_mem» := P2M_GroundTheory_Heights__Heights_SectionCycle_cross_mem_b4bbd6c8875a
