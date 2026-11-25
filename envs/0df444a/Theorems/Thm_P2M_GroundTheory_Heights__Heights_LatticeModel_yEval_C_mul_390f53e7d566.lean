-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_yEval_C_mul_390f53e7d566
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_yEval_C_mul_390f53e7d566
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:08.229988+00:00
-- url     : https://prove2.me/theorems/cda319c9-3cb2-4d04-89f0-e242c4ab5373
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model y Eval C mul 390f53e7d566: P2 M Ground Theory Heights  Heights Lattice Model y Eval C mul 390f53e7d566
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model y Eval C mul 390f53e7d566 construction uses the P2 M Ground Theory Heights  Heights Lattice Model y Eval C mul 390f53e7d566 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean#L179-L181

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_yEval_C_mul_390f53e7d566 (k : ℤ) (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) :
    yEval φ (C k * g) = k * yEval φ g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«yEval_C_mul» := P2M_GroundTheory_Heights__Heights_LatticeModel_yEval_C_mul_390f53e7d566
