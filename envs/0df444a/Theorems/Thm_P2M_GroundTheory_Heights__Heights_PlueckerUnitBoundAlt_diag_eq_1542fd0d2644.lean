-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_diag_eq_1542fd0d2644
-- name    : P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_diag_eq_1542fd0d2644
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:39.5998+00:00
-- url     : https://prove2.me/theorems/61a2a610-2a79-481f-af26-be5a9801a3c6
-- title:
--   P2 M Ground Theory Heights  Heights Pluecker Unit Bound Alt diag eq 1542fd0d2644: P2 M Ground Theory Heights  Heights Pluecker Unit Bound Alt diag eq 1542fd0d2644
-- statement:
--   The P2 M Ground Theory Heights  Heights Pluecker Unit Bound Alt diag eq 1542fd0d2644 construction uses the P2 M Ground Theory Heights  Heights Pluecker Unit Bound Alt diag eq 1542fd0d2644 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPlueckerUnitBound.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPlueckerUnitBound.lean#L16-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerUnitBound
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
open Matrix Finset
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.PlueckerUnitBoundAlt

theorem P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_diag_eq_1542fd0d2644 {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, ‖Z a b‖ = 1) (a : Fin j) :
    (1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a = (((1 + m : ℝ)) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlueckerUnitBoundAlt».«diag_eq» := P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_diag_eq_1542fd0d2644
