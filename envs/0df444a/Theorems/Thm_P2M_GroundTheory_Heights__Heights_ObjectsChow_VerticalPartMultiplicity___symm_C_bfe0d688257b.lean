-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_C_bfe0d688257b
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_C_bfe0d688257b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:12:42.208866+00:00
-- url     : https://prove2.me/theorems/88bd49a1-80da-4178-8203-5712036751de
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   symm C bfe0d688257b: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   symm C bfe0d688257b
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   symm C bfe0d688257b construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity   symm C bfe0d688257b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L113-L114

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_C_bfe0d688257b (a : 𝓞 ℚ) : (Ψ n).symm (C a) = C (ι.symm a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«Ψ_symm_C» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_C_bfe0d688257b
