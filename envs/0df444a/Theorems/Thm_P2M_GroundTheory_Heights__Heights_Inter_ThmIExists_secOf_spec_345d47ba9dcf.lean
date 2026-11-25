-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_secOf_spec_345d47ba9dcf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_secOf_spec_345d47ba9dcf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:03.531543+00:00
-- url     : https://prove2.me/theorems/95157df7-c303-4d1f-8065-db1889de16db
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists sec Of spec 345d47ba9dcf: P2 M Ground Theory Heights  Heights Inter Thm IExists sec Of spec 345d47ba9dcf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists sec Of spec 345d47ba9dcf construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists sec Of spec 345d47ba9dcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L70-L74

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_secOf_spec_345d47ba9dcf {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    IsMultiHomog (secOf P b) b ∧ secOf P b ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«secOf_spec» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_secOf_spec_345d47ba9dcf
