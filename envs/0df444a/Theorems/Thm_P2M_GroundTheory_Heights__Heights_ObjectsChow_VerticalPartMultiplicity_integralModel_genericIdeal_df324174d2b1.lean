-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_integralModel_genericIdeal_df324174d2b1
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_integralModel_genericIdeal_df324174d2b1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:23.903903+00:00
-- url     : https://prove2.me/theorems/ff3b766c-3e76-529c-aa01-56a2a3edf3b2
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity integral Model generic Ideal df324174d2b1: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity integ
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity integral Model generic Ideal df324174d2b1 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity integral Model generic Ideal df324174d2b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L181-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L181-L216

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_integralModel_genericIdeal_df324174d2b1 (P : Ideal (MRing (PBlk n))) [hP : P.IsPrime]
    (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal P) :
    integralModel (genericIdeal P) = P.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«integralModel_genericIdeal» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_integralModel_genericIdeal_df324174d2b1
