-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_weight_one_eq_degree_27ee5a5b405e
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_weight_one_eq_degree_27ee5a5b405e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:43.467767+00:00
-- url     : https://prove2.me/theorems/d1fdff07-00fa-4510-b07f-f0b9dc96bff6
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model weight one eq degree 27ee5a5b405e: P2 M Ground Theory Heights  Heights Lattice Model weight one eq degree 27ee5a5b405e
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model weight one eq degree 27ee5a5b405e construction uses the P2 M Ground Theory Heights  Heights Lattice Model weight one eq degree 27ee5a5b405e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L114-L116

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
variable {R : Type*} [CommSemiring R]

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_weight_one_eq_degree_27ee5a5b405e {σ : Type*} (s : σ →₀ ℕ) : Finsupp.weight (1 : σ → ℕ) s = s.degree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«weight_one_eq_degree» := P2M_GroundTheory_Heights__Heights_LatticeModel_weight_one_eq_degree_27ee5a5b405e
