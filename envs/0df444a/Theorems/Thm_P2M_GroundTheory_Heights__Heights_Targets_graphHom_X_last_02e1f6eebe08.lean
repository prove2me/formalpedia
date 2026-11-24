-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_last_02e1f6eebe08
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_last_02e1f6eebe08
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:15.081798+00:00
-- url     : https://prove2.me/theorems/8bbef134-5ec9-49b1-ba2d-5dd68b120834
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Hom X last 02e1f6eebe08: P2 M Ground Theory Heights  Heights Targets graph Hom X last 02e1f6eebe08
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Hom X last 02e1f6eebe08 construction uses the P2 M Ground Theory Heights  Heights Targets graph Hom X last 02e1f6eebe08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L28-L29

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

theorem P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_last_02e1f6eebe08 (p : MvPolynomial (Fin n) ℂ) : graphHom p (X (Fin.last n)) = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphHom_X_last» := P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_last_02e1f6eebe08
