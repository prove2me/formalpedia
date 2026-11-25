-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ptTwo_eq_comap_680e3cb3445e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ptTwo_eq_comap_680e3cb3445e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:24.810967+00:00
-- url     : https://prove2.me/theorems/da417a42-05e3-4b58-8fee-3bf2b1127f49
-- title:
--   P2 M Ground Theory Heights  Heights Inter pt Two eq comap 680e3cb3445e: P2 M Ground Theory Heights  Heights Inter pt Two eq comap 680e3cb3445e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pt Two eq comap 680e3cb3445e construction uses the P2 M Ground Theory Heights  Heights Inter pt Two eq comap 680e3cb3445e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L190-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L190-L199

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_ptTwo_eq_comap_680e3cb3445e :
    ptTwo = (inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2))).comap redTwo := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ptTwo_eq_comap» := P2M_GroundTheory_Heights__Heights_Inter_ptTwo_eq_comap_680e3cb3445e
