-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_isPrime_disjoint_5dfc671a0d1a
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_isPrime_disjoint_5dfc671a0d1a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:31.282324+00:00
-- url     : https://prove2.me/theorems/5e639555-77aa-432d-a70e-e6fa2341ad1e
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal fin Ideal is Prime disjoint 5dfc671a0d1a: P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal fin Ideal is Prime d
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal fin Ideal is Prime disjoint 5dfc671a0d1a construction uses the P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Ideal fin Ideal is Prime disjoint 5dfc671a0d1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean#L46-L59

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_isPrime_disjoint_5dfc671a0d1a (n d : ℕ) (P : Ideal (MRing (PBlk n))) (hP : IsArithVar P d) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).IsPrime ∧
      Disjoint ((intUnits n : Set (MvPolynomial (Fin n) ℤ))) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«GenericFibreIdeal».«finIdeal_isPrime_disjoint» := P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_isPrime_disjoint_5dfc671a0d1a
