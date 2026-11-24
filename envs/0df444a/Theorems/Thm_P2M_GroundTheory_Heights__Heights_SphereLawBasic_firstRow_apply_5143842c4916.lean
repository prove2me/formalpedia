-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_apply_5143842c4916
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_apply_5143842c4916
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:59.745283+00:00
-- url     : https://prove2.me/theorems/574e6ef9-073a-4ba3-ae31-2c5505e5109f
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law Basic first Row apply 5143842c4916: P2 M Ground Theory Heights  Heights Sphere Law Basic first Row apply 5143842c4916
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law Basic first Row apply 5143842c4916 construction uses the P2 M Ground Theory Heights  Heights Sphere Law Basic first Row apply 5143842c4916 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic
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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawBasic

theorem P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_apply_5143842c4916 (N : ℕ) (u : Fin 1 × Fin N → ℂ) (j : Fin N) : firstRow N u j = u (0, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawBasic».«firstRow_apply» := P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_apply_5143842c4916
