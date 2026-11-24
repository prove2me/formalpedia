-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:03.230789+00:00
-- url     : https://prove2.me/theorems/93af1b3d-2acc-499e-8b08-8a4d7d6bd8cb
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Hom surjective d83f19d508e8: P2 M Ground Theory Heights  Heights Targets graph Hom surjective d83f19d508e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Hom surjective d83f19d508e8 construction uses the P2 M Ground Theory Heights  Heights Targets graph Hom surjective d83f19d508e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L37-L38

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

theorem P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8 (p : MvPolynomial (Fin n) ℂ) : Function.Surjective (graphHom p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphHom_surjective» := P2M_GroundTheory_Heights__Heights_Targets_graphHom_surjective_d83f19d508e8
