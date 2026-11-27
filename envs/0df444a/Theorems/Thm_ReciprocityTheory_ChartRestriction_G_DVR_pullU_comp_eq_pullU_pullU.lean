-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_comp_eq_pullU_pullU
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pullU_comp_eq_pullU_pullU
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:11:49.855227+00:00
-- url     : https://prove2.me/theorems/f4f58319-0fba-4227-ad54-2cd5b2e1d44b
-- title:
--   DVR: pull U comp eq pull U pull U
-- statement:
--   The DVR construction uses the pull U comp eq pull U pull U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/AppCompatGeneric.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/AppCompatGeneric.lean#L15-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.DVR.pullU_comp_eq_pullU_pullU (h : Z ⟶ Y) (ψ : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (h ≫ ψ) U x = pullU h (ψ ⁻¹ᵁ U) (pullU ψ U x) := by sorry
