-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_iSupIndep_comap_c20b593583ec
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_iSupIndep_comap_c20b593583ec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:53.672614+00:00
-- url     : https://prove2.me/theorems/7e7f463f-7e9b-5d7f-9a30-bd4e8a3172d9
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot i Sup Indep comap c20b593583ec: P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot i Sup Indep comap c20b593583ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot i Sup Indep comap c20b593583ec construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot i Sup Indep comap c20b593583ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L15-L25

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_iSupIndep_comap_c20b593583ec {R N M : Type*} [Ring R] [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    {κ : Type*} {p : κ → Submodule R M} (hp : iSupIndep p) (g : N →ₗ[R] M) (hg : Function.Injective g) :
    iSupIndep fun i => (p i).comap g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GradedSubquot».«iSupIndep_comap» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_iSupIndep_comap_c20b593583ec
