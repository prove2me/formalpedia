-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_smul_mem_latticeDual_7ca10bc0ad16
-- name    : P2M_GroundTheory_Heights__Heights_exists_int_smul_mem_latticeDual_7ca10bc0ad16
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:53.204382+00:00
-- url     : https://prove2.me/theorems/c88c6511-6ab7-4c9b-9a35-fabf41625800
-- title:
--   P2 M Ground Theory Heights  Heights exists int smul mem lattice Dual 7ca10bc0ad16: P2 M Ground Theory Heights  Heights exists int smul mem lattice Dual 7ca10bc0ad16
-- statement:
--   The P2 M Ground Theory Heights  Heights exists int smul mem lattice Dual 7ca10bc0ad16 construction uses the P2 M Ground Theory Heights  Heights exists int smul mem lattice Dual 7ca10bc0ad16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L13-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L13-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_exists_int_smul_mem_latticeDual_7ca10bc0ad16 {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (hL : L.FG)
    (v : Fin m → K) : ∃ D : ℤ, D ≠ 0 ∧ D • v ∈ latticeDual L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_int_smul_mem_latticeDual» := P2M_GroundTheory_Heights__Heights_exists_int_smul_mem_latticeDual_7ca10bc0ad16
