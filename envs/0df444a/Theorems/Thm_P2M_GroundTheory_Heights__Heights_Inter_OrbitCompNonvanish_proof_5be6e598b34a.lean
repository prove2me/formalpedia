-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_proof_5be6e598b34a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_proof_5be6e598b34a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:28.750739+00:00
-- url     : https://prove2.me/theorems/12919bce-0ee9-46c3-822a-cf6b4dd543b5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Orbit Comp Nonvanish proof 5be6e598b34a: P2 M Ground Theory Heights  Heights Inter Orbit Comp Nonvanish proof 5be6e598b34a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Orbit Comp Nonvanish proof 5be6e598b34a construction uses the P2 M Ground Theory Heights  Heights Inter Orbit Comp Nonvanish proof 5be6e598b34a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/POrbitCompNonvanish.lean#L36-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/POrbitCompNonvanish.lean#L36-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_POrbitCompNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_proof_5be6e598b34a : OrbitCompNonvanish.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«OrbitCompNonvanish».«proof» := P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_proof_5be6e598b34a
