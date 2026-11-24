-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_X_ne_zero_6e1224960199
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_X_ne_zero_6e1224960199
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:02.269153+00:00
-- url     : https://prove2.me/theorems/da3f271b-fe6f-4326-b5ec-632ff16c2fad
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle mk F X ne zero 6e1224960199: P2 M Ground Theory Heights  Heights Section Cycle mk F X ne zero 6e1224960199
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle mk F X ne zero 6e1224960199 construction uses the P2 M Ground Theory Heights  Heights Section Cycle mk F X ne zero 6e1224960199 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L212-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L212-L214

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_X_ne_zero_6e1224960199 {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«mkF_X_ne_zero» := P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_X_ne_zero_6e1224960199
