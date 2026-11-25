-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_exists_form_not_mem_587f4c48195d
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_exists_form_not_mem_587f4c48195d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:55.63585+00:00
-- url     : https://prove2.me/theorems/6f358cd1-e0b8-45e6-b2b4-fab0dba3cea0
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle exists form not mem 587f4c48195d: P2 M Ground Theory Heights  Heights Section Cycle exists form not mem 587f4c48195d
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle exists form not mem 587f4c48195d construction uses the P2 M Ground Theory Heights  Heights Section Cycle exists form not mem 587f4c48195d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L274-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L274-L306

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_exists_form_not_mem_587f4c48195d (hg : D.IsFormSystem d g) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {W : Ideal (MvPolynomial (Coord D.extSizes) ℤ)} [W.IsPrime] (hPW : D.extIdeal ≤ W)
    (hW : ∀ k, (X (D.oldCoord ⟨k, c k⟩) : MvPolynomial _ ℤ) ∉ W) :
    ∃ i, D.liftOld (g c i) ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«exists_form_not_mem» := P2M_GroundTheory_Heights__Heights_SectionCycle_exists_form_not_mem_587f4c48195d
