-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Via_algebraMap_apply_2ab0efe72b9a
-- name    : P2M_GroundTheory_Heights__Heights_Via_algebraMap_apply_2ab0efe72b9a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:41:02.977868+00:00
-- url     : https://prove2.me/theorems/504e4718-b800-434c-8a18-0d46b408022a
-- title:
--   P2 M Ground Theory Heights  Heights Via algebra Map apply 2ab0efe72b9a: P2 M Ground Theory Heights  Heights Via algebra Map apply 2ab0efe72b9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Via algebra Map apply 2ab0efe72b9a construction uses the P2 M Ground Theory Heights  Heights Via algebra Map apply 2ab0efe72b9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L25-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean#L25-L25

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
open GroundTheory.Heights₂.Heights.Via
variable {R : Type*} [CommRing R] (φ : R →+* ℂ)

theorem P2M_GroundTheory_Heights__Heights_Via_algebraMap_apply_2ab0efe72b9a (r : R) : algebraMap R (Via φ) r = ofComplex φ (φ r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Via».«algebraMap_apply» := P2M_GroundTheory_Heights__Heights_Via_algebraMap_apply_2ab0efe72b9a
