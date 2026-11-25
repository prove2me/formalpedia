-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_comap_C_e18d6e2b5341
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_comap_C_e18d6e2b5341
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:20.643943+00:00
-- url     : https://prove2.me/theorems/07067fd9-1453-4c48-9d84-aeda6d4a41da
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity fin Ideal comap C e18d6e2b5341: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity fin Ideal comap
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity fin Ideal comap C e18d6e2b5341 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity fin Ideal comap C e18d6e2b5341 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L175-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L175-L179

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_comap_C_e18d6e2b5341 (P : Ideal (MRing (PBlk n))) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) =
      P.comap (C : ℤ →+* MRing (PBlk n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«finIdeal_comap_C» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_comap_C_e18d6e2b5341
