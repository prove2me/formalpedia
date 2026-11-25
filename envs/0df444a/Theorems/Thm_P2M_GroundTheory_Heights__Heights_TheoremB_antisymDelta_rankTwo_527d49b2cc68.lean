-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_antisymDelta_rankTwo_527d49b2cc68
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_antisymDelta_rankTwo_527d49b2cc68
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:15.892715+00:00
-- url     : https://prove2.me/theorems/f1146b8b-f49d-41a9-968a-9c59d981843f
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B antisym Delta rank Two 527d49b2cc68: P2 M Ground Theory Heights  Heights Theorem B antisym Delta rank Two 527d49b2cc68
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B antisym Delta rank Two 527d49b2cc68 construction uses the P2 M Ground Theory Heights  Heights Theorem B antisym Delta rank Two 527d49b2cc68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L408-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L408-L411

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

theorem P2M_GroundTheory_Heights__Heights_TheoremB_antisymDelta_rankTwo_527d49b2cc68 : antisymDelta (Fin d1.f) d1.N = (X (0, 0) - X (0, 1) : LamPoly d1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«antisymDelta_rankTwo» := P2M_GroundTheory_Heights__Heights_TheoremB_antisymDelta_rankTwo_527d49b2cc68
