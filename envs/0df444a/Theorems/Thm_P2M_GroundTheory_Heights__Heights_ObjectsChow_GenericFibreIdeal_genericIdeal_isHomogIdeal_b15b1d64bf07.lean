-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_genericIdeal_isHomogIdeal_b15b1d64bf07
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_genericIdeal_isHomogIdeal_b15b1d64bf07
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:41.980216+00:00
-- url     : https://prove2.me/theorems/b97b64ba-9c08-4950-a5b7-d8ae1f0127df
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal generic Ideal is Homog Ideal b15b1d64bf07: P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal generic Ideal is Ho
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal generic Ideal is Homog Ideal b15b1d64bf07 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal generic Ideal is Homog Ideal b15b1d64bf07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean#L65-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean#L65-L81

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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_genericIdeal_isHomogIdeal_b15b1d64bf07 (P : Ideal (MRing (PBlk n)))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P) : IsHomogIdeal (genericIdeal P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«GenericFibreIdeal».«genericIdeal_isHomogIdeal» := P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_genericIdeal_isHomogIdeal_b15b1d64bf07
