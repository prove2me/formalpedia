-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_frac_unit_locRing_ee3966325a70
-- name    : P2M_GroundTheory_Heights__Heights_Inter_frac_unit_locRing_ee3966325a70
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:33.750919+00:00
-- url     : https://prove2.me/theorems/08018ec9-1864-5835-87b6-fb156a044d76
-- title:
--   P2 M Ground Theory Heights  Heights Inter frac unit loc Ring ee3966325a70: P2 M Ground Theory Heights  Heights Inter frac unit loc Ring ee3966325a70
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter frac unit loc Ring ee3966325a70 construction uses the P2 M Ground Theory Heights  Heights Inter frac unit loc Ring ee3966325a70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L82-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L82-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_frac_unit_locRing_ee3966325a70 {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (huW : u ∉ W) (hvW : v ∉ W) [P.IsPrime]
    {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W ∧ ∃ z ∈ locRing P W, y * z = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«frac_unit_locRing» := P2M_GroundTheory_Heights__Heights_Inter_frac_unit_locRing_ee3966325a70
