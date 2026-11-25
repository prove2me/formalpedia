-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_isClosed_rootHyperplane_5ca09dd4c102
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_isClosed_rootHyperplane_5ca09dd4c102
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:28.94157+00:00
-- url     : https://prove2.me/theorems/fb6516b4-f185-55df-bd51-474b0da9da2a
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B is Closed root Hyperplane 5ca09dd4c102: P2 M Ground Theory Heights  Heights Theorem B is Closed root Hyperplane 5ca09dd4c102
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B is Closed root Hyperplane 5ca09dd4c102 construction uses the P2 M Ground Theory Heights  Heights Theorem B is Closed root Hyperplane 5ca09dd4c102 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L373-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L373-L374

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)

theorem P2M_GroundTheory_Heights__Heights_TheoremB_isClosed_rootHyperplane_5ca09dd4c102 (τ : Fin d.f) (a b : Fin d.N) : IsClosed (rootHyperplane d τ a b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«isClosed_rootHyperplane» := P2M_GroundTheory_Heights__Heights_TheoremB_isClosed_rootHyperplane_5ca09dd4c102
