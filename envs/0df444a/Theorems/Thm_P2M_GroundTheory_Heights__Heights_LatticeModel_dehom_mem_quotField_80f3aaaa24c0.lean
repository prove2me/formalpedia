-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_mem_quotField_80f3aaaa24c0
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_mem_quotField_80f3aaaa24c0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:51.809852+00:00
-- url     : https://prove2.me/theorems/3c00464f-c716-4cf5-a411-b1dc85e1c9df
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model dehom mem quot Field 80f3aaaa24c0: P2 M Ground Theory Heights  Heights Lattice Model dehom mem quot Field 80f3aaaa24c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model dehom mem quot Field 80f3aaaa24c0 construction uses the P2 M Ground Theory Heights  Heights Lattice Model dehom mem quot Field 80f3aaaa24c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L223-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L223-L238

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
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_mem_quotField_80f3aaaa24c0 (hL : L.FG) (hφ : IsDualBasis L φ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) ∈ quotField φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«dehom_mem_quotField» := P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_mem_quotField_80f3aaaa24c0
