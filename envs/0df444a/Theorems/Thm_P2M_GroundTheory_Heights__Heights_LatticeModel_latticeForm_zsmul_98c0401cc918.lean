-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_zsmul_98c0401cc918
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_zsmul_98c0401cc918
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:37.355091+00:00
-- url     : https://prove2.me/theorems/fb57b687-a58a-427e-b39a-49a3552878bd
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model lattice Form zsmul 98c0401cc918: P2 M Ground Theory Heights  Heights Lattice Model lattice Form zsmul 98c0401cc918
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model lattice Form zsmul 98c0401cc918 construction uses the P2 M Ground Theory Heights  Heights Lattice Model lattice Form zsmul 98c0401cc918 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L65-L69

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
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_zsmul_98c0401cc918 (c : ℤ) (u : Fin m → K) : latticeForm (c • u) = C (c : K) * latticeForm u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«latticeForm_zsmul» := P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_zsmul_98c0401cc918
