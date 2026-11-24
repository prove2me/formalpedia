-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_mul_1c4c584656fe
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_mul_1c4c584656fe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:44.0088+00:00
-- url     : https://prove2.me/theorems/76c8994f-7fef-4552-b167-bca4fa2e4071
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists sec mul 1c4c584656fe: P2 M Ground Theory Heights  Heights Inter Thm IExists sec mul 1c4c584656fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists sec mul 1c4c584656fe construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists sec mul 1c4c584656fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L76-L83

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_mul_1c4c584656fe {P : Ideal (MRing ι)} (hpr : P.IsPrime) {A B : HermLine ι} {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) : IsSectionOn P (A.tensor B) (s * t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«sec_mul» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_mul_1c4c584656fe
