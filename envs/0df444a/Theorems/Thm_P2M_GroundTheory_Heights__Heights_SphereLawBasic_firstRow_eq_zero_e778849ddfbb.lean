-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_eq_zero_e778849ddfbb
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_eq_zero_e778849ddfbb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:20.571074+00:00
-- url     : https://prove2.me/theorems/a551185a-8654-4b2b-aa9f-e3ba24a53cdc
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law Basic first Row eq zero e778849ddfbb: P2 M Ground Theory Heights  Heights Sphere Law Basic first Row eq zero e778849ddfbb
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law Basic first Row eq zero e778849ddfbb construction uses the P2 M Ground Theory Heights  Heights Sphere Law Basic first Row eq zero e778849ddfbb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean#L27-L32

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

theorem P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_eq_zero_e778849ddfbb (N : ℕ) (u : Fin 1 × Fin N → ℂ) (h : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0) :
    firstRow N u = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawBasic».«firstRow_eq_zero» := P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_eq_zero_e778849ddfbb
