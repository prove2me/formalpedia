-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_surjective_da448e31549d
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_surjective_da448e31549d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:19.27323+00:00
-- url     : https://prove2.me/theorems/606df2e6-993f-595f-a052-6ee62ac1dc6c
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Subst surjective da448e31549d: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Subst surjective da448e31549d
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Subst surjective da448e31549d construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Subst surjective da448e31549d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L69-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
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
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_surjective_da448e31549d (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Function.Surjective (graphSubst p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«graphSubst_surjective» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_surjective_da448e31549d
