-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_isMultiHomog_iff_98f435e2c05f
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_isMultiHomog_iff_98f435e2c05f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:38.486992+00:00
-- url     : https://prove2.me/theorems/ea6d0e3d-928d-4b20-a492-7e4b4ba36214
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model is Multi Homog iff 98f435e2c05f: P2 M Ground Theory Heights  Heights Lattice Model is Multi Homog iff 98f435e2c05f
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model is Multi Homog iff 98f435e2c05f construction uses the P2 M Ground Theory Heights  Heights Lattice Model is Multi Homog iff 98f435e2c05f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L260-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L260-L273

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_isMultiHomog_iff_98f435e2c05f (g : Geo.MRing (blockIdx fun _ : Unit ↦ N)) (d : Unit → ℕ) :
    Geo.IsMultiHomog g d ↔ g.IsHomogeneous (d ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_LatticeModel_isMultiHomog_iff_98f435e2c05f
