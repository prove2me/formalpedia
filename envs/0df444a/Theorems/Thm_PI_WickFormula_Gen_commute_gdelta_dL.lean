-- Prove2me | Theorems.Thm_PI_WickFormula_Gen_commute_gdelta_dL
-- name    : PI.WickFormula.Gen.commute_gdelta_dL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:53.387519+00:00
-- url     : https://prove2.me/theorems/8d9530d2-0c2e-4109-bd20-79e949fc6aae
-- title:
--   Gen: commute gdelta d L
-- statement:
--   The Gen construction uses the commute gdelta d L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenPow.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/GenPow.lean#L39-L42

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

theorem PI.WickFormula.Gen.commute_gdelta_dL (κ : I → J → K) (i : I) : Commute (gdelta κ) (dL κ i) := by sorry
