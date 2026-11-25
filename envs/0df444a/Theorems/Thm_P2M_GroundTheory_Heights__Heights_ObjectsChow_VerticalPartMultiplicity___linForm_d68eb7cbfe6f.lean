-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___linForm_d68eb7cbfe6f
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___linForm_d68eb7cbfe6f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:27.93686+00:00
-- url     : https://prove2.me/theorems/33d00b62-0fa8-4cc0-903c-37280d004ba4
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   lin Form d68eb7cbfe6f: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   lin Form d68eb7cbfe6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   lin Form d68eb7cbfe6f construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   lin Form d68eb7cbfe6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L121-L123

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___linForm_d68eb7cbfe6f (u : Fin n → ℤ) :
    Ψ n (IndefiniteRowSideFullHecke.ArithBezout.linForm u) = linForm (fun j => ((u j : ℤ) : 𝓞 ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«Ψ_linForm» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___linForm_d68eb7cbfe6f
