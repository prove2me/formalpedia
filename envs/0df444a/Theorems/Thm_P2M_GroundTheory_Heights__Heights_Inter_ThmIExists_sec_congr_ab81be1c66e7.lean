-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_congr_ab81be1c66e7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_congr_ab81be1c66e7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:21.147813+00:00
-- url     : https://prove2.me/theorems/0471dad1-292e-443e-9dc3-804a6fce1909
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists sec congr ab81be1c66e7: P2 M Ground Theory Heights  Heights Inter Thm IExists sec congr ab81be1c66e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists sec congr ab81be1c66e7 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists sec congr ab81be1c66e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L85-L86

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_congr_ab81be1c66e7 {P : Ideal (MRing ι)} {A B : HermLine ι} {s : MRing ι} (h : A = B)
    (hs : IsSectionOn P A s) : IsSectionOn P B s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«sec_congr» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_congr_ab81be1c66e7
