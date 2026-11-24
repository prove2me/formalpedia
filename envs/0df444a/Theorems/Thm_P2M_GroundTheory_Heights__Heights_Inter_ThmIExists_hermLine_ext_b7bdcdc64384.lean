-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hermLine_ext_b7bdcdc64384
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hermLine_ext_b7bdcdc64384
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:48.319522+00:00
-- url     : https://prove2.me/theorems/82cdf17b-b306-46b0-b30c-e018a8480573
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists herm Line ext b7bdcdc64384: P2 M Ground Theory Heights  Heights Inter Thm IExists herm Line ext b7bdcdc64384
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists herm Line ext b7bdcdc64384 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists herm Line ext b7bdcdc64384 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L16-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hermLine_ext_b7bdcdc64384 {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«hermLine_ext» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hermLine_ext_b7bdcdc64384
