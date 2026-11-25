-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratStandard_latticeMetricAgrees_b5791eb021fc
-- name    : P2M_GroundTheory_Heights__Heights_ratStandard_latticeMetricAgrees_b5791eb021fc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:11.343801+00:00
-- url     : https://prove2.me/theorems/6eb350de-6777-5aff-b612-fc8ff0552f34
-- title:
--   P2 M Ground Theory Heights  Heights rat Standard lattice Metric Agrees b5791eb021fc: P2 M Ground Theory Heights  Heights rat Standard lattice Metric Agrees b5791eb021fc
-- statement:
--   The P2 M Ground Theory Heights  Heights rat Standard lattice Metric Agrees b5791eb021fc construction uses the P2 M Ground Theory Heights  Heights rat Standard lattice Metric Agrees b5791eb021fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L109-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/DualModel.lean#L109-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel
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
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_ratStandard_latticeMetricAgrees_b5791eb021fc (r : ℕ) :
    LatticeMetricAgrees (fun j : Fin (r + 1) ↦ (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ))
      (HermLattice.standard ℚ (r + 1)) (HermLine.standard (fun _ : Unit ↦ r)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ratStandard_latticeMetricAgrees» := P2M_GroundTheory_Heights__Heights_ratStandard_latticeMetricAgrees_b5791eb021fc
