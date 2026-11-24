-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_mkF_e1a919750cdc
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_mkF_e1a919750cdc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:43.279697+00:00
-- url     : https://prove2.me/theorems/5bc57c43-2b41-494d-8272-e4ab99ed12c0
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom mk F e1a919750cdc: P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom mk F e1a919750cdc
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom mk F e1a919750cdc construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge fun Hom mk F e1a919750cdc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L76-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_mkF_e1a919750cdc (f : MvPolynomial (Coord n) ℤ) : funHom P y hP (P.mkF f) = coneHom y f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«funHom_mkF» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_mkF_e1a919750cdc
