-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mem_quotField_f112b4739b83
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_mem_quotField_f112b4739b83
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:40.576247+00:00
-- url     : https://prove2.me/theorems/cd05fee2-ac42-4855-960b-2e64974e1f93
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model mem quot Field f112b4739b83: P2 M Ground Theory Heights  Heights Lattice Model mem quot Field f112b4739b83
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model mem quot Field f112b4739b83 construction uses the P2 M Ground Theory Heights  Heights Lattice Model mem quot Field f112b4739b83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L240-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L240-L258

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_mem_quotField_f112b4739b83 (hL : L.FG) (hφ : IsDualBasis L φ) (s : LatticeField K r) : s ∈ quotField φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«mem_quotField» := P2M_GroundTheory_Heights__Heights_LatticeModel_mem_quotField_f112b4739b83
