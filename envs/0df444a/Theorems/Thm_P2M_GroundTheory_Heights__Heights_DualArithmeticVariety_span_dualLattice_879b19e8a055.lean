-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_dualLattice_879b19e8a055
-- name    : P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_dualLattice_879b19e8a055
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:08.452559+00:00
-- url     : https://prove2.me/theorems/b325b793-aeeb-4a93-a56c-c73d210c7a0f
-- title:
--   P2 M Ground Theory Heights  Heights Dual Arithmetic Variety span dual Lattice 879b19e8a055: P2 M Ground Theory Heights  Heights Dual Arithmetic Variety span dual Lattice 879b19e8a055
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Arithmetic Variety span dual Lattice 879b19e8a055 construction uses the P2 M Ground Theory Heights  Heights Dual Arithmetic Variety span dual Lattice 879b19e8a055 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L59-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L59-L86

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

theorem P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_dualLattice_879b19e8a055 (F : HermLattice K i) :
    Submodule.span K (dualLattice F : Set (Fin i → K)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualArithmeticVariety».«span_dualLattice» := P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_span_dualLattice_879b19e8a055
