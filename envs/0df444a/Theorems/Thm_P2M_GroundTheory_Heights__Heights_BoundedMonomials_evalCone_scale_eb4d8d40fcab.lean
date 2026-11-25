-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_scale_eb4d8d40fcab
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_scale_eb4d8d40fcab
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:04.402885+00:00
-- url     : https://prove2.me/theorems/184e9b45-60f4-4c30-9ffd-d412da4ac71f
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone scale eb4d8d40fcab: P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone scale eb4d8d40fcab
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone scale eb4d8d40fcab construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone scale eb4d8d40fcab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L31-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_scale_eb4d8d40fcab {F : Type*} [CommRing F] (u : ι → F) (z : Cone n F)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    evalCone (fun k i ↦ u k * z k i) f = (∏ k, u k ^ δ k) * evalCone z f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«evalCone_scale» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_scale_eb4d8d40fcab
