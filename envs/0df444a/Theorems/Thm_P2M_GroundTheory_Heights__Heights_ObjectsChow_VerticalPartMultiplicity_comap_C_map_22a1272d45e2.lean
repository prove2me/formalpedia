-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_comap_C_map_22a1272d45e2
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_comap_C_map_22a1272d45e2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:12:23.69635+00:00
-- url     : https://prove2.me/theorems/ffa44909-4933-49fb-9260-75c63605554d
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity comap C map 22a1272d45e2: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity comap C map 22a1272d45
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity comap C map 22a1272d45e2 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity comap C map 22a1272d45e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L136-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L136-L143

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_comap_C_map_22a1272d45e2 (W : Ideal (MRing (PBlk n))) :
    (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) =
      (W.comap (C : ℤ →+* MRing (PBlk n))).map (ι : ℤ →+* 𝓞 ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«comap_C_map» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_comap_C_map_22a1272d45e2
