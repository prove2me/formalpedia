-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_X_bd364b1db4a5
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_X_bd364b1db4a5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:33.918278+00:00
-- url     : https://prove2.me/theorems/063d2f6f-53d6-4fc8-872f-b979b58d073b
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone X bd364b1db4a5: P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone X bd364b1db4a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone X bd364b1db4a5 construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone X bd364b1db4a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L57-L59

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_X_bd364b1db4a5 {F : Type*} [CommRing F] (z : Cone n F) (k : ι) (i : Fin (n k + 1)) :
    evalCone z (X ⟨k, i⟩) = z k i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«evalCone_X» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_X_bd364b1db4a5
