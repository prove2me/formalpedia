-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeMap_intComb_ac9dfce53bdd
-- name    : P2M_GroundTheory_Heights__Heights_latticeMap_intComb_ac9dfce53bdd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:51.098795+00:00
-- url     : https://prove2.me/theorems/129fd6ba-af1d-481b-854b-f3bf4cb17931
-- title:
--   P2 M Ground Theory Heights  Heights lattice Map int Comb ac9dfce53bdd: P2 M Ground Theory Heights  Heights lattice Map int Comb ac9dfce53bdd
-- statement:
--   The P2 M Ground Theory Heights  Heights lattice Map int Comb ac9dfce53bdd construction uses the P2 M Ground Theory Heights  Heights lattice Map int Comb ac9dfce53bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L171-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L171-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_latticeMap_intComb_ac9dfce53bdd (φ : Fin (N + 1) → Fin (r + 1) → K) (c : Fin (N + 1) → ℤ) :
    latticeMap φ (∑ b, (c b : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * X ⟨(), b⟩) =
      latticeForm (∑ b, c b • φ b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«latticeMap_intComb» := P2M_GroundTheory_Heights__Heights_latticeMap_intComb_ac9dfce53bdd
