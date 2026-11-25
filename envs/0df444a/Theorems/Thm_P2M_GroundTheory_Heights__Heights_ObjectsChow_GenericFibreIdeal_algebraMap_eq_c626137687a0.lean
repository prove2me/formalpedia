-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_algebraMap_eq_c626137687a0
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_algebraMap_eq_c626137687a0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:40.829849+00:00
-- url     : https://prove2.me/theorems/e1ac92c1-dc32-515f-927a-8f213470e15f
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal algebra Map eq c626137687a0: P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal algebra Map eq c626137687a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal algebra Map eq c626137687a0 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal algebra Map eq c626137687a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean#L34-L38

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
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_algebraMap_eq_c626137687a0 :
    algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«GenericFibreIdeal».«algebraMap_eq» := P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_algebraMap_eq_c626137687a0
