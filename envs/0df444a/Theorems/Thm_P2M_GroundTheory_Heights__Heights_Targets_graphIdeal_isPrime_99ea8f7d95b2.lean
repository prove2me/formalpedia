-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_isPrime_99ea8f7d95b2
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_isPrime_99ea8f7d95b2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:40.682859+00:00
-- url     : https://prove2.me/theorems/6902e1d8-0a49-51f6-8440-caf419b3bebc
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Ideal is Prime 99ea8f7d95b2: P2 M Ground Theory Heights  Heights Targets graph Ideal is Prime 99ea8f7d95b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Ideal is Prime 99ea8f7d95b2 construction uses the P2 M Ground Theory Heights  Heights Targets graph Ideal is Prime 99ea8f7d95b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L59-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_isPrime_99ea8f7d95b2 {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphIdeal_isPrime» := P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_isPrime_99ea8f7d95b2
