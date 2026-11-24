-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1
-- name    : P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:45.449194+00:00
-- url     : https://prove2.me/theorems/f56734be-3062-4576-b4d2-f9f6daf5b42e
-- title:
--   P2 M Ground Theory Heights  Heights Dual Arithmetic Variety dual Lattice Coord eq ca49334a53b1: P2 M Ground Theory Heights  Heights Dual Arithmetic Variety dual Lattice Coord eq ca49334a53b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Arithmetic Variety dual Lattice Coord eq ca49334a53b1 construction uses the P2 M Ground Theory Heights  Heights Dual Arithmetic Variety dual Lattice Coord eq ca49334a53b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L98-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]
variable [NumberField K] {i : ℕ}
variable {F : HermLattice K i} {T : Type}

theorem P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1 (b : Module.Basis T ℤ (dualLattice F)) (t : T) :
    dualLatticeCoord b ⟨(), t⟩ = evalForm i (b t : Fin i → K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualArithmeticVariety».«dualLatticeCoord_eq» := P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1
