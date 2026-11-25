-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_eq_map_0fa9df26c3a7
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_eq_map_0fa9df26c3a7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:30.758753+00:00
-- url     : https://prove2.me/theorems/d765866d-3f89-4b46-a3f7-249b86165d31
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal fin Ideal eq map 0fa9df26c3a7: P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal fin Ideal eq map 0fa9df26c3a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal fin Ideal eq map 0fa9df26c3a7 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal fin Ideal eq map 0fa9df26c3a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean#L27-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreIdeal
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
open GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_eq_map_0fa9df26c3a7 (P : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = P.map (blkRingEquiv n).symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«GenericFibreIdeal».«finIdeal_eq_map» := P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_eq_map_0fa9df26c3a7
