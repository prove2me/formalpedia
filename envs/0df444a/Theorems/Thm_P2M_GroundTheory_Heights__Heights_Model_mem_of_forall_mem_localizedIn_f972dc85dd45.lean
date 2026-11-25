-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_of_forall_mem_localizedIn_f972dc85dd45
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_of_forall_mem_localizedIn_f972dc85dd45
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:47.821055+00:00
-- url     : https://prove2.me/theorems/bb558b01-edd0-4c53-b202-59e6eb0ef7f7
-- title:
--   P2 M Ground Theory Heights  Heights Model mem of forall mem localized In f972dc85dd45: P2 M Ground Theory Heights  Heights Model mem of forall mem localized In f972dc85dd45
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem of forall mem localized In f972dc85dd45 construction uses the P2 M Ground Theory Heights  Heights Model mem of forall mem localized In f972dc85dd45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLatticesAgree.lean#L16-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLatticesAgree.lean#L16-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLatticesAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

theorem P2M_GroundTheory_Heights__Heights_Model_mem_of_forall_mem_localizedIn_f972dc85dd45 (hHOI : HeightOneIntersection.Statement)
    [IsNoetherianRing A] [IsIntegrallyClosed A] (M : Submodule A V) [Module.Projective A M]
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V)
    (hv : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → v ∈ localizedIn p.asIdeal M) : v ∈ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_of_forall_mem_localizedIn» := P2M_GroundTheory_Heights__Heights_Model_mem_of_forall_mem_localizedIn_f972dc85dd45
