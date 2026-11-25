-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_exists_form_7820841f3e38
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_exists_form_7820841f3e38
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:37.053207+00:00
-- url     : https://prove2.me/theorems/944f022a-b4b3-5e97-bf0b-84ca2f7a1aec
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists exists form 7820841f3e38: P2 M Ground Theory Heights  Heights Inter Thm IExists exists form 7820841f3e38
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists exists form 7820841f3e38 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists exists form 7820841f3e38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L54-L63

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_exists_form_7820841f3e38 {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    ∃ s : MRing ι, IsMultiHomog s b ∧ s ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«exists_form» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_exists_form_7820841f3e38
