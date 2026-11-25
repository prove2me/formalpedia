-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_coordMonomial_not_mem_f731ea15fea9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_coordMonomial_not_mem_f731ea15fea9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:57.826841+00:00
-- url     : https://prove2.me/theorems/f34718cd-ba00-414a-860a-910753630798
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IUnique coord Monomial not mem f731ea15fea9: P2 M Ground Theory Heights  Heights Inter Thm IUnique coord Monomial not mem f731ea15fea9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IUnique coord Monomial not mem f731ea15fea9 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IUnique coord Monomial not mem f731ea15fea9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L82-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIUnique
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
open GroundTheory.Heights₂.Heights.Inter.ThmIUnique
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_coordMonomial_not_mem_f731ea15fea9 {P : Ideal (MRing ι)} (hP : P.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIUnique».«coordMonomial_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_coordMonomial_not_mem_f731ea15fea9
