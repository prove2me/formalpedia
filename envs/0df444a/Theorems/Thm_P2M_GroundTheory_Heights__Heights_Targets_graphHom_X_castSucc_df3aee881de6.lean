-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_castSucc_df3aee881de6
-- name    : P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_castSucc_df3aee881de6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:07.615958+00:00
-- url     : https://prove2.me/theorems/4c66b11c-35e1-45d5-a7da-9d7d1d46c952
-- title:
--   P2 M Ground Theory Heights  Heights Targets graph Hom X cast Succ df3aee881de6: P2 M Ground Theory Heights  Heights Targets graph Hom X cast Succ df3aee881de6
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets graph Hom X cast Succ df3aee881de6 construction uses the P2 M Ground Theory Heights  Heights Targets graph Hom X cast Succ df3aee881de6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L24-L26

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

theorem P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_castSucc_df3aee881de6 (p : MvPolynomial (Fin n) ℂ) (i : Fin n) :
    graphHom p (X (Fin.castSucc i)) = X i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«graphHom_X_castSucc» := P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_castSucc_df3aee881de6
