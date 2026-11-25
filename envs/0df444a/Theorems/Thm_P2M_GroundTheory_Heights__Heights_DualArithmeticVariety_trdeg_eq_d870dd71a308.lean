-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_trdeg_eq_d870dd71a308
-- name    : P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_trdeg_eq_d870dd71a308
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:44.443256+00:00
-- url     : https://prove2.me/theorems/4dc345c8-a4a7-595e-a066-a51019c55d43
-- title:
--   P2 M Ground Theory Heights  Heights Dual Arithmetic Variety trdeg eq d870dd71a308: P2 M Ground Theory Heights  Heights Dual Arithmetic Variety trdeg eq d870dd71a308
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Arithmetic Variety trdeg eq d870dd71a308 construction uses the P2 M Ground Theory Heights  Heights Dual Arithmetic Variety trdeg eq d870dd71a308 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L52-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]

theorem P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_trdeg_eq_d870dd71a308 (m : ℕ) : Cardinal.mk (Fin m) = Algebra.trdeg K (ProjField K m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualArithmeticVariety».«trdeg_eq» := P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_trdeg_eq_d870dd71a308
