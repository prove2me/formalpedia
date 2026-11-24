-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_mul_5bfd3b05f445
-- name    : P2M_GroundTheory_Heights__Heights_evalCone_mul_5bfd3b05f445
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:48:03.558712+00:00
-- url     : https://prove2.me/theorems/14489623-3b8f-4084-a574-709fb383d52d
-- title:
--   P2 M Ground Theory Heights  Heights eval Cone mul 5bfd3b05f445: P2 M Ground Theory Heights  Heights eval Cone mul 5bfd3b05f445
-- statement:
--   The P2 M Ground Theory Heights  Heights eval Cone mul 5bfd3b05f445 construction uses the P2 M Ground Theory Heights  Heights eval Cone mul 5bfd3b05f445 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L159-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L159-L160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_evalCone_mul_5bfd3b05f445 {F : Type*} [CommRing F] (z : Cone n F) (f g : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * g) = evalCone z f * evalCone z g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«evalCone_mul» := P2M_GroundTheory_Heights__Heights_evalCone_mul_5bfd3b05f445
