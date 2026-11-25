-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_exists_common_denom_4d33b8a3a3b0
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_exists_common_denom_4d33b8a3a3b0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:21.985829+00:00
-- url     : https://prove2.me/theorems/39740c53-f119-5efc-8926-1bb544552f43
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle exists common denom 4d33b8a3a3b0: P2 M Ground Theory Heights  Heights Section Cycle exists common denom 4d33b8a3a3b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle exists common denom 4d33b8a3a3b0 construction uses the P2 M Ground Theory Heights  Heights Section Cycle exists common denom 4d33b8a3a3b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L247-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L247-L255

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_exists_common_denom_4d33b8a3a3b0 {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {m : ℕ} {u : Fin m → P.FunField} (hu : ∀ j, u j ∈ P.chartRing c) :
    ∃ (E : ℕ) (f : Fin m → MvPolynomial (Coord n) ℤ),
      ∀ j, u j * P.mkF (chartMonomial c 1) ^ E = P.mkF (f j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«exists_common_denom» := P2M_GroundTheory_Heights__Heights_SectionCycle_exists_common_denom_4d33b8a3a3b0
