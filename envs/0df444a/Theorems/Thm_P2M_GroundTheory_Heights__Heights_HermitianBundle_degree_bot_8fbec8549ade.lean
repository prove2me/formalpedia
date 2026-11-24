-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_bot_8fbec8549ade
-- name    : P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_bot_8fbec8549ade
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:05.900841+00:00
-- url     : https://prove2.me/theorems/498794b2-c831-4257-a793-3a9cf6afd923
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Bundle degree bot 8fbec8549ade: P2 M Ground Theory Heights  Heights Hermitian Bundle degree bot 8fbec8549ade
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Bundle degree bot 8fbec8549ade construction uses the P2 M Ground Theory Heights  Heights Hermitian Bundle degree bot 8fbec8549ade property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FiniteSupportHeight.lean#L85-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FiniteSupportHeight.lean#L85-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
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
open MvPolynomial NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_bot_8fbec8549ade {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K) :
    E.degree ⊥ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianBundle».«degree_bot» := P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_bot_8fbec8549ade
