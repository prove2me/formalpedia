-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_intSmul_1c54165cdeb0
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_intSmul_1c54165cdeb0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:57.550432+00:00
-- url     : https://prove2.me/theorems/087b8beb-0ae9-4cee-9642-f6a7ddcf157a
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form int Smul 1c54165cdeb0: P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form int Smul 1c54165cdeb0
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form int Smul 1c54165cdeb0 construction uses the P2 M Ground Theory Heights  Heights Lattice Model dehom lattice Form int Smul 1c54165cdeb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L183-L186

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_intSmul_1c54165cdeb0 (k : ℤ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm ((k : K) • u)) = k * dehom K r (latticeForm u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«dehom_latticeForm_intSmul» := P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_intSmul_1c54165cdeb0
