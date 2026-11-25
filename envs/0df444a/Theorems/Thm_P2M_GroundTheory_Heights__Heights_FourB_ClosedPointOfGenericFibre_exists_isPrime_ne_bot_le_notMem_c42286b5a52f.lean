-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_isPrime_ne_bot_le_notMem_c42286b5a52f
-- name    : P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_isPrime_ne_bot_le_notMem_c42286b5a52f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:00.574723+00:00
-- url     : https://prove2.me/theorems/0ba7d1fd-2f9d-5e30-b63c-78ff9922819a
-- title:
--   P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre exists is Prime ne bot le not Mem c42286b5a52f: P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre exists
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre exists is Prime ne bot le not Mem c42286b5a52f construction uses the P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre exists is Prime ne bot le not Mem c42286b5a52f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L120-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L120-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PClosedPointOfGenericFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
open GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre

theorem P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_isPrime_ne_bot_le_notMem_c42286b5a52f {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (M : Ideal R) [M.IsPrime] (hM : 2 ≤ M.height) (t : R) (ht : t ≠ 0) :
    ∃ P : Ideal R, P.IsPrime ∧ P ≠ ⊥ ∧ P ≤ M ∧ t ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«ClosedPointOfGenericFibre».«exists_isPrime_ne_bot_le_notMem» := P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_isPrime_ne_bot_le_notMem_c42286b5a52f
