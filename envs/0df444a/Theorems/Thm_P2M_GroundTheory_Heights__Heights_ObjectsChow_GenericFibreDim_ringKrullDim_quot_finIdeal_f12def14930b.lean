-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_ringKrullDim_quot_finIdeal_f12def14930b
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_ringKrullDim_quot_finIdeal_f12def14930b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:03.0834+00:00
-- url     : https://prove2.me/theorems/38fefd73-a97e-4b14-a6d8-3be6cbe80ec9
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim ring Krull Dim quot fin Ideal f12def14930b: P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim ring Krull Dim quot fi
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim ring Krull Dim quot fin Ideal f12def14930b construction uses the P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim ring Krull Dim quot fin Ideal f12def14930b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreDim.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreDim.lean#L31-L37

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_ringKrullDim_quot_finIdeal_f12def14930b {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    ringKrullDim (MvPolynomial (Fin n) ℤ ⧸ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) =
      ringKrullDim (MRing (PBlk n) ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«GenericFibreDim».«ringKrullDim_quot_finIdeal» := P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_ringKrullDim_quot_finIdeal_f12def14930b
