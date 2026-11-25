-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_iSupIndep_map_of_ker_le_353158e21bdf
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_iSupIndep_map_of_ker_le_353158e21bdf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:58.716552+00:00
-- url     : https://prove2.me/theorems/653e51fb-8ac8-50b4-a8f7-105f53f47d20
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot i Sup Indep map of ker le 353158e21bdf: P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot i Sup Indep map of ker le 35
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot i Sup Indep map of ker le 353158e21bdf construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot i Sup Indep map of ker le 353158e21bdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L27-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L27-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_iSupIndep_map_of_ker_le_353158e21bdf {R N Q : Type*} [Ring R] [AddCommGroup N] [AddCommGroup Q] [Module R N]
    [Module R Q] {κ : Type*} {p : κ → Submodule R N} (hp : iSupIndep p) (f : N →ₗ[R] Q)
    (hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ p c)) :
    iSupIndep fun i => (p i).map f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GradedSubquot».«iSupIndep_map_of_ker_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_iSupIndep_map_of_ker_le_353158e21bdf
