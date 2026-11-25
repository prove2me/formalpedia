-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regRing_intCast_coe_2b169ec58805
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regRing_intCast_coe_2b169ec58805
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:43.058228+00:00
-- url     : https://prove2.me/theorems/820adf19-5667-48e9-992a-e3a7417e2b69
-- title:
--   P2 M Ground Theory Heights  Heights Inter reg Ring int Cast coe 2b169ec58805: P2 M Ground Theory Heights  Heights Inter reg Ring int Cast coe 2b169ec58805
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter reg Ring int Cast coe 2b169ec58805 construction uses the P2 M Ground Theory Heights  Heights Inter reg Ring int Cast coe 2b169ec58805 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldExistsInv.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldExistsInv.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeOfHeightMapEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldExistsInv
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

theorem P2M_GroundTheory_Heights__Heights_Inter_regRing_intCast_coe_2b169ec58805 (P : Ideal (MRing ι)) (n : ℤ) :
    (((n : regRing P) : funField P) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regRing_intCast_coe» := P2M_GroundTheory_Heights__Heights_Inter_regRing_intCast_coe_2b169ec58805
