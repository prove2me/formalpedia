-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___apply_a3d15408a314
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___apply_a3d15408a314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:06.494566+00:00
-- url     : https://prove2.me/theorems/41d1b8d9-e925-4ec6-8b76-f1762bbb63f2
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   apply a3d15408a314: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   apply a3d15408a314
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   apply a3d15408a314 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   apply a3d15408a314 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L102-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___apply_a3d15408a314 (f : MRing (PBlk n)) :
    Ψ n f = MvPolynomial.map (ι : ℤ →+* 𝓞 ℚ) (rename (eb n).symm f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«Ψ_apply» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___apply_a3d15408a314
