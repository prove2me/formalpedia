-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_eq_map_4a676a9bfd34
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_eq_map_4a676a9bfd34
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:01.398805+00:00
-- url     : https://prove2.me/theorems/8fa2b6c6-ac5c-484a-b7a6-ffbed1e12434
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity fin Ideal eq map 4a676a9bfd34: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity fin Ideal eq map
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity fin Ideal eq map 4a676a9bfd34 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity fin Ideal eq map 4a676a9bfd34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L125-L129

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_eq_map_4a676a9bfd34 (W : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal W =
      W.map ((renameEquiv ℤ (eb n)).symm.toRingEquiv : MRing (PBlk n) →+* MvPolynomial (Fin n) ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«finIdeal_eq_map» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_eq_map_4a676a9bfd34
