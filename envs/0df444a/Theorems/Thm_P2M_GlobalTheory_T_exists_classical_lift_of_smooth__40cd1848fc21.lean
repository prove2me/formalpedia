-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_classical_lift_of_smooth__40cd1848fc21
-- name    : P2M_GlobalTheory_T_exists_classical_lift_of_smooth__40cd1848fc21
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:14.718797+00:00
-- url     : https://prove2.me/theorems/04b5994b-6af8-4b95-928a-9fe1e35a4820
-- title:
--   P2 M Global Theory T exists classical lift of smooth  40cd1848fc21: P2 M Global Theory T exists classical lift of smooth  40cd1848fc21
-- statement:
--   The P2 M Global Theory T exists classical lift of smooth  40cd1848fc21 construction uses the P2 M Global Theory T exists classical lift of smooth  40cd1848fc21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsClassicalLiftOfSmoothStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsClassicalLiftOfSmoothStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsClassicalLiftOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsClassicalLiftOfSmoothStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem P2M_GlobalTheory_T_exists_classical_lift_of_smooth__40cd1848fc21 : ∀ (p : ℕ) [Fact p.Prime] (X S : Scheme.{0}) (f : X ⟶ S) [Smooth f] (y : Sp (OO p) ⟶ S) (x : Sp (kb p) ⟶ X), x ≫ f = rPt p ≫ y → ∃ b : Sp (OO p) ⟶ X, b ≫ f = y ∧ rPt p ≫ b = x := by sorry

alias «GlobalTheory».«T».«exists_classical_lift_of_smooth'» := P2M_GlobalTheory_T_exists_classical_lift_of_smooth__40cd1848fc21
