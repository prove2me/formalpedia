-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_1c75dcc245cd
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_1c75dcc245cd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:04.233854+00:00
-- url     : https://prove2.me/theorems/559fd44a-c8d5-412d-a08e-f5832f6d68e7
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle ext Map lift Old 1c75dcc245cd: P2 M Ground Theory Heights  Heights Section Cycle ext Map lift Old 1c75dcc245cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle ext Map lift Old 1c75dcc245cd construction uses the P2 M Ground Theory Heights  Heights Section Cycle ext Map lift Old 1c75dcc245cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L158-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L158-L163

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_1c75dcc245cd {h : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hh : IsWeightedHomogeneous (coordDeg n) h δ) :
    D.extMap (D.liftOld h) = C (P.mkF h) * ∏ k, X (some k) ^ δ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«extMap_liftOld» := P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_1c75dcc245cd
