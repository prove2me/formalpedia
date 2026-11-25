-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_up_95943556fabe
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_up_95943556fabe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:35.151802+00:00
-- url     : https://prove2.me/theorems/4571af28-b398-4788-b0a5-fe5dfae46137
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists is Section On up 95943556fabe: P2 M Ground Theory Heights  Heights Inter Thm IExists is Section On up 95943556fabe
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists is Section On up 95943556fabe construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists is Section On up 95943556fabe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L100-L103

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_up_95943556fabe {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (A : HermLine ι) :
    IsSectionOn P (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«isSectionOn_up» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_up_95943556fabe
