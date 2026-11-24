-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mul_mem_prodSpan_f0c3d551bff6
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_mul_mem_prodSpan_f0c3d551bff6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:47.760268+00:00
-- url     : https://prove2.me/theorems/e5de0dd0-364f-4cb5-8ad7-4bfc43f4d4a8
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model mul mem prod Span f0c3d551bff6: P2 M Ground Theory Heights  Heights Lattice Model mul mem prod Span f0c3d551bff6
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model mul mem prod Span f0c3d551bff6 construction uses the P2 M Ground Theory Heights  Heights Lattice Model mul mem prod Span f0c3d551bff6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L27-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L27-L50

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_mul_mem_prodSpan_f0c3d551bff6 {a b : ℕ} {p q : MvPolynomial (Fin m) K} (hp : p ∈ prodSpan L a)
    (hq : q ∈ prodSpan L b) : p * q ∈ prodSpan L (a + b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«mul_mem_prodSpan» := P2M_GroundTheory_Heights__Heights_LatticeModel_mul_mem_prodSpan_f0c3d551bff6
