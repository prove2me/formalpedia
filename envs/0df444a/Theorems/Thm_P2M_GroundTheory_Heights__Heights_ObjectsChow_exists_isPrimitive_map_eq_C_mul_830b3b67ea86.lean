-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_isPrimitive_map_eq_C_mul_830b3b67ea86
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_isPrimitive_map_eq_C_mul_830b3b67ea86
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:15.546408+00:00
-- url     : https://prove2.me/theorems/d36127b3-fb55-48c6-9f11-28f00f5618df
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow exists is Primitive map eq C mul 830b3b67ea86: P2 M Ground Theory Heights  Heights Objects Chow exists is Primitive map eq C mul 830b3b67ea86
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow exists is Primitive map eq C mul 830b3b67ea86 construction uses the P2 M Ground Theory Heights  Heights Objects Chow exists is Primitive map eq C mul 830b3b67ea86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIntChowFormExists.lean#L31-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIntChowFormExists.lean#L31-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIntChowFormExists
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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_isPrimitive_map_eq_C_mul_830b3b67ea86 {σ : Type*} (g : MvPolynomial σ ℚ) (hg : g ≠ 0) :
    ∃ a : ℚ, a ≠ 0 ∧ ∃ f : MvPolynomial σ ℤ, IndefiniteRowSideFullHecke.ArithBezout.IsPrimitive f ∧
      map (Int.castRingHom ℚ) f = C a * g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«exists_isPrimitive_map_eq_C_mul» := P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_isPrimitive_map_eq_C_mul_830b3b67ea86
