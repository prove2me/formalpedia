-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_rename_9e3a36680299
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphHom_rename_9e3a36680299
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:00.467808+00:00
-- url     : https://prove2.me/theorems/9b722a99-884d-42b9-8e4b-f031e205d973
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Hom rename 9e3a36680299: P2 M Ground Theory Heights  Heights Targets graph Hom rename 9e3a36680299
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Hom rename 9e3a36680299 construction uses the P2 M Ground Theory Heights  Heights Targets graph Hom rename 9e3a36680299 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L31-L35

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

theorem P2M_GroundTheory_Heights__Heights_Targets_graphHom_rename_9e3a36680299 (p q : MvPolynomial (Fin n) ℂ) : graphHom p (rename Fin.castSucc q) = q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphHom_rename» := P2M_GroundTheory_Heights__Heights_Targets_graphHom_rename_9e3a36680299
