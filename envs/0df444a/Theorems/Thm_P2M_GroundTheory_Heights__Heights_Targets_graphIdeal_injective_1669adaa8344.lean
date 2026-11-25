-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_injective_1669adaa8344
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_injective_1669adaa8344
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:28.78065+00:00
-- url     : https://prove2.me/theorems/5107f390-b75e-5cda-8764-188405a9dd57
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Ideal injective 1669adaa8344: P2 M Ground Theory Heights  Heights Targets graph Ideal injective 1669adaa8344
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Ideal injective 1669adaa8344 construction uses the P2 M Ground Theory Heights  Heights Targets graph Ideal injective 1669adaa8344 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L119-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L119-L120

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

theorem P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_injective_1669adaa8344 (p : MvPolynomial (Fin n) ℂ) : Function.Injective (fun W => graphIdeal W p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphIdeal_injective» := P2M_GroundTheory_Heights__Heights_Targets_graphIdeal_injective_1669adaa8344
