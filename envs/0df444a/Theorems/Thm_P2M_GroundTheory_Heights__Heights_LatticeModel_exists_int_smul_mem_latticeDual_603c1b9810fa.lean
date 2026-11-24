-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_smul_mem_latticeDual_603c1b9810fa
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_smul_mem_latticeDual_603c1b9810fa
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:30.110995+00:00
-- url     : https://prove2.me/theorems/d9627252-6163-4672-ac21-a1e04b0d746a
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model exists int smul mem lattice Dual 603c1b9810fa: P2 M Ground Theory Heights  Heights Lattice Model exists int smul mem lattice Dual 603c1b9810fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model exists int smul mem lattice Dual 603c1b9810fa construction uses the P2 M Ground Theory Heights  Heights Lattice Model exists int smul mem lattice Dual 603c1b9810fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L25-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L25-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_smul_mem_latticeDual_603c1b9810fa {m : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} (hL : L.FG)
    (u : Fin m → K) : ∃ n : ℤ, n ≠ 0 ∧ (n : K) • u ∈ latticeDual L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«exists_int_smul_mem_latticeDual» := P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_smul_mem_latticeDual_603c1b9810fa
