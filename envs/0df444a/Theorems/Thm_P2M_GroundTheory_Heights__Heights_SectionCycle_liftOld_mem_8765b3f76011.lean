-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_mem_8765b3f76011
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_mem_8765b3f76011
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:15.711834+00:00
-- url     : https://prove2.me/theorems/66cba2b1-d4b3-4a5d-853c-248edd649358
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle lift Old mem 8765b3f76011: P2 M Ground Theory Heights  Heights Section Cycle lift Old mem 8765b3f76011
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle lift Old mem 8765b3f76011 construction uses the P2 M Ground Theory Heights  Heights Section Cycle lift Old mem 8765b3f76011 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L170-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L170-L176

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_mem_8765b3f76011 {p : MvPolynomial (Coord n) ℤ} (hp : p ∈ P.ideal) : D.liftOld p ∈ D.extIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«liftOld_mem» := P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_mem_8765b3f76011
