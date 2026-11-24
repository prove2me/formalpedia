-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_basis_ac0e3eb82930
-- name    : P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_basis_ac0e3eb82930
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:52.274971+00:00
-- url     : https://prove2.me/theorems/a2b4feb6-c36a-431d-bc0e-3d2ca50fda99
-- title:
--   P2 M Ground Theory Heights  Heights Dual Arithmetic Variety span basis ac0e3eb82930: P2 M Ground Theory Heights  Heights Dual Arithmetic Variety span basis ac0e3eb82930
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Arithmetic Variety span basis ac0e3eb82930 construction uses the P2 M Ground Theory Heights  Heights Dual Arithmetic Variety span basis ac0e3eb82930 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L90-L96

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

theorem P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_basis_ac0e3eb82930 [Fintype T] (b : Module.Basis T ℤ (dualLattice F)) :
    Submodule.span K (Set.range fun t => (b t : Fin i → K)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualArithmeticVariety».«span_basis» := P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_basis_ac0e3eb82930
