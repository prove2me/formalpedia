-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_finIdeal_eq_comap_eead2ee5270f
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_finIdeal_eq_comap_eead2ee5270f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:28.006317+00:00
-- url     : https://prove2.me/theorems/c50a7b9d-f5de-4c7c-9812-33fecd2547ac
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim fin Ideal eq comap eead2ee5270f: P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim fin Ideal eq comap eead2ee5270f
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim fin Ideal eq comap eead2ee5270f construction uses the P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim fin Ideal eq comap eead2ee5270f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreDim.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreDim.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreDim
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
open GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_finIdeal_eq_comap_eead2ee5270f {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = P.comap (blkRingEquiv n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«GenericFibreDim».«finIdeal_eq_comap» := P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_finIdeal_eq_comap_eead2ee5270f
