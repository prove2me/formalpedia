-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_X_7aa01944f7d0
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_X_7aa01944f7d0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:47.907871+00:00
-- url     : https://prove2.me/theorems/b52398b2-8c5b-4edf-8180-34387ffbf968
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   symm X 7aa01944f7d0: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   symm X 7aa01944f7d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   symm X 7aa01944f7d0 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   symm X 7aa01944f7d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L116-L117

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_X_7aa01944f7d0 (i : Fin n) : (Ψ n).symm (X i) = X ⟨(), i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«Ψ_symm_X» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_X_7aa01944f7d0
