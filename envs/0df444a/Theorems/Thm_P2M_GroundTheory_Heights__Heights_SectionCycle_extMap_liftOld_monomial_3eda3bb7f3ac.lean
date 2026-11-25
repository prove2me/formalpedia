-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_monomial_3eda3bb7f3ac
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_monomial_3eda3bb7f3ac
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:14.204978+00:00
-- url     : https://prove2.me/theorems/93d4d757-cbec-56c8-ba67-5fc73f8ea3e7
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle ext Map lift Old monomial 3eda3bb7f3ac: P2 M Ground Theory Heights  Heights Section Cycle ext Map lift Old monomial 3eda3bb7f3ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle ext Map lift Old monomial 3eda3bb7f3ac construction uses the P2 M Ground Theory Heights  Heights Section Cycle ext Map lift Old monomial 3eda3bb7f3ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L145-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L145-L156

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_monomial_3eda3bb7f3ac (s : Coord n →₀ ℕ) (a : ℤ) :
    D.extMap (D.liftOld (monomial s a)) =
      C (P.mkF (monomial s a)) * ∏ k, X (some k) ^ (Finsupp.weight (coordDeg n) s k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«extMap_liftOld_monomial» := P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_monomial_3eda3bb7f3ac
