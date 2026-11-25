-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_DualLatticeMultiple_proof_499a36cc5a42
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_DualLatticeMultiple_proof_499a36cc5a42
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:55.22921+00:00
-- url     : https://prove2.me/theorems/d1216575-48ba-540b-a795-208ec583cee2
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Dual Lattice Multiple proof 499a36cc5a42: P2 M Ground Theory Heights  Heights Finite Covolume Dual Lattice Multiple proof 499a36cc5a42
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Dual Lattice Multiple proof 499a36cc5a42 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Dual Lattice Multiple proof 499a36cc5a42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDualLatticeMultiple.lean#L40-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDualLatticeMultiple.lean#L40-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StDualLatticeMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDualLatticeMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_DualLatticeMultiple_proof_499a36cc5a42 (h : HermitianForm F E W) : DualLatticeMultiple.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«DualLatticeMultiple».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_DualLatticeMultiple_proof_499a36cc5a42
