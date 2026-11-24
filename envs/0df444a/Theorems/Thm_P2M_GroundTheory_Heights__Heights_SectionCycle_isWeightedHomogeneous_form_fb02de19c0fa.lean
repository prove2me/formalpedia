-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_isWeightedHomogeneous_form_fb02de19c0fa
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_isWeightedHomogeneous_form_fb02de19c0fa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:43.88652+00:00
-- url     : https://prove2.me/theorems/820896d3-a11c-498e-ac96-214d5a09955a
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle is Weighted Homogeneous form fb02de19c0fa: P2 M Ground Theory Heights  Heights Section Cycle is Weighted Homogeneous form fb02de19c0fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle is Weighted Homogeneous form fb02de19c0fa construction uses the P2 M Ground Theory Heights  Heights Section Cycle is Weighted Homogeneous form fb02de19c0fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L180-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L180-L187

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

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_isWeightedHomogeneous_form_fb02de19c0fa (hg : D.IsFormSystem d g) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (D.size + 1)) :
    IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ ((d k : ℤ) + D.deg k).toNat) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«isWeightedHomogeneous_form» := P2M_GroundTheory_Heights__Heights_SectionCycle_isWeightedHomogeneous_form_fb02de19c0fa
