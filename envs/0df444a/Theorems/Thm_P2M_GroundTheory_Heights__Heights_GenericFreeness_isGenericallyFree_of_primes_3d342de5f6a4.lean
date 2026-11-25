-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_primes_3d342de5f6a4
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_primes_3d342de5f6a4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:22.170723+00:00
-- url     : https://prove2.me/theorems/bd80a40b-a858-4c9f-a957-073bee7c2268
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of primes 3d342de5f6a4: P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of primes 3d342de5f6a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of primes 3d342de5f6a4 construction uses the P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of primes 3d342de5f6a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreeness.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreeness.lean#L15-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreeness
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
open MvPolynomial
universe u v w
open GroundTheory.Heights₂.Heights.GenericFreeness

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_primes_3d342de5f6a4 {A : Type u} [CommRing A] [IsDomain A] {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Algebra A R] (hq : ∀ p : PrimeSpectrum R, IsGenericallyFree A (R ⧸ p.asIdeal))
    (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] [Module.Finite R M] :
    IsGenericallyFree A M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«isGenericallyFree_of_primes» := P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_primes_3d342de5f6a4
