-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_exists_clear_denom_13403b1d4dce
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_exists_clear_denom_13403b1d4dce
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:11.660469+00:00
-- url     : https://prove2.me/theorems/fff619f9-595a-460e-b9dd-149d1b2a81db
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle exists clear denom 13403b1d4dce: P2 M Ground Theory Heights  Heights Section Cycle exists clear denom 13403b1d4dce
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle exists clear denom 13403b1d4dce construction uses the P2 M Ground Theory Heights  Heights Section Cycle exists clear denom 13403b1d4dce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L216-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L216-L245

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_exists_clear_denom_13403b1d4dce {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (e : ℕ) (f : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ e = P.mkF f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«exists_clear_denom» := P2M_GroundTheory_Heights__Heights_SectionCycle_exists_clear_denom_13403b1d4dce
