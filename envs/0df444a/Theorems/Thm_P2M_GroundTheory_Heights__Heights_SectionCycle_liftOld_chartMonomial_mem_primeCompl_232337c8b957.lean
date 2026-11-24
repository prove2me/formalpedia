-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_chartMonomial_mem_primeCompl_232337c8b957
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_chartMonomial_mem_primeCompl_232337c8b957
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:11.59033+00:00
-- url     : https://prove2.me/theorems/11869c2b-b5d8-4291-b193-091cc88a908b
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle lift Old chart Monomial mem prime Compl 232337c8b957: P2 M Ground Theory Heights  Heights Section Cycle lift Old chart Monomial mem prime Compl 232337
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle lift Old chart Monomial mem prime Compl 232337c8b957 construction uses the P2 M Ground Theory Heights  Heights Section Cycle lift Old chart Monomial mem prime Compl 232337c8b957 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L266-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L266-L272

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_chartMonomial_mem_primeCompl_232337c8b957 {W : Ideal (MvPolynomial (Coord D.extSizes) ℤ)} [W.IsPrime]
    {c : (k : ι) → Fin (n k + 1)} (hW : ∀ k, (X (D.oldCoord ⟨k, c k⟩) : MvPolynomial _ ℤ) ∉ W)
    (e : ι → ℕ) : D.liftOld (chartMonomial c e) ∈ W.primeCompl := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«liftOld_chartMonomial_mem_primeCompl» := P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_chartMonomial_mem_primeCompl_232337c8b957
