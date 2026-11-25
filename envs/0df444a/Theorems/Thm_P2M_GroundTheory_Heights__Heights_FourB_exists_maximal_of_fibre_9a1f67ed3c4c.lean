-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_exists_maximal_of_fibre_9a1f67ed3c4c
-- name    : P2M_GroundTheory_Heights__Heights_FourB_exists_maximal_of_fibre_9a1f67ed3c4c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:02.494809+00:00
-- url     : https://prove2.me/theorems/38089c6f-b9b7-4c6e-b6ad-4847bf5ef54d
-- title:
--   P2 M Ground Theory Heights  Heights Four B exists maximal of fibre 9a1f67ed3c4c: P2 M Ground Theory Heights  Heights Four B exists maximal of fibre 9a1f67ed3c4c
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B exists maximal of fibre 9a1f67ed3c4c construction uses the P2 M Ground Theory Heights  Heights Four B exists maximal of fibre 9a1f67ed3c4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointThroughPrime.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointThroughPrime.lean#L11-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointThroughPrime
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

theorem P2M_GroundTheory_Heights__Heights_FourB_exists_maximal_of_fibre_9a1f67ed3c4c (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal R)
    (u : R) (hP : P.IsPrime) (hPv : P.comap (algebraMap (𝓞 F) R) = v.asIdeal) (hu : u ∉ P) :
    ∃ M : Ideal R, M.IsMaximal ∧ P ≤ M ∧ u ∉ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«exists_maximal_of_fibre» := P2M_GroundTheory_Heights__Heights_FourB_exists_maximal_of_fibre_9a1f67ed3c4c
