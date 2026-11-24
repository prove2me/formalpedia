-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_one_mem_prodSpan_zero_c23367664238
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_one_mem_prodSpan_zero_c23367664238
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:21.641795+00:00
-- url     : https://prove2.me/theorems/c2119ece-4ff7-46bc-9313-01013e79bcbb
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model one mem prod Span zero c23367664238: P2 M Ground Theory Heights  Heights Lattice Model one mem prod Span zero c23367664238
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model one mem prod Span zero c23367664238 construction uses the P2 M Ground Theory Heights  Heights Lattice Model one mem prod Span zero c23367664238 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L20-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
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
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_one_mem_prodSpan_zero_c23367664238 : (1 : MvPolynomial (Fin m) K) ∈ prodSpan L 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«one_mem_prodSpan_zero» := P2M_GroundTheory_Heights__Heights_LatticeModel_one_mem_prodSpan_zero_c23367664238
