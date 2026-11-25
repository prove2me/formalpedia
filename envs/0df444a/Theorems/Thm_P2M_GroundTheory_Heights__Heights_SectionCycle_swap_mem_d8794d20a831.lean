-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_swap_mem_d8794d20a831
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_swap_mem_d8794d20a831
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:36.565799+00:00
-- url     : https://prove2.me/theorems/0a7608d4-7512-514d-8faf-d823f4efbd93
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle swap mem d8794d20a831: P2 M Ground Theory Heights  Heights Section Cycle swap mem d8794d20a831
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle swap mem d8794d20a831 construction uses the P2 M Ground Theory Heights  Heights Section Cycle swap mem d8794d20a831 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L201-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L201-L208

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_swap_mem_d8794d20a831 (hg : D.IsFormSystem d g) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (i j : Fin (D.size + 1)) :
    D.liftOld (g c i) * X (D.newCoord j) - D.liftOld (g c j) * X (D.newCoord i) ∈ D.extIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«swap_mem» := P2M_GroundTheory_Heights__Heights_SectionCycle_swap_mem_d8794d20a831
