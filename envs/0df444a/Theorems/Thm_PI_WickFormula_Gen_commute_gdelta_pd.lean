-- Prove2me | Theorems.Thm_PI_WickFormula_Gen_commute_gdelta_pd
-- name    : PI.WickFormula.Gen.commute_gdelta_pd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:47.14481+00:00
-- url     : https://prove2.me/theorems/0a0f8b14-fd20-5aa7-99f2-87fc96ae1315
-- title:
--   Gen: commute gdelta pd
-- statement:
--   The Gen construction uses the commute gdelta pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenPow.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenPow.lean#L33-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem PI.WickFormula.Gen.commute_gdelta_pd (κ : I → J → K) (c : I ⊕ J) : Commute (gdelta κ) (pd c) := by sorry
