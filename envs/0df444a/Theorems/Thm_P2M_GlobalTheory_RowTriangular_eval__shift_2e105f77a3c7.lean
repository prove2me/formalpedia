-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RowTriangular_eval__shift_2e105f77a3c7
-- name    : P2M_GlobalTheory_RowTriangular_eval__shift_2e105f77a3c7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:25.295941+00:00
-- url     : https://prove2.me/theorems/df0ef651-5743-4da7-9f38-83079d1b7b14
-- title:
--   P2 M Global Theory Row Triangular eval  shift 2e105f77a3c7: P2 M Global Theory Row Triangular eval  shift 2e105f77a3c7
-- statement:
--   The P2 M Global Theory Row Triangular eval  shift 2e105f77a3c7 construction uses the P2 M Global Theory Row Triangular eval  shift 2e105f77a3c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/InvariantOperatorValueTriangularChange.lean#L26-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/InvariantOperatorValueTriangularChange.lean#L26-L59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RowTriangular
open MvPolynomial
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k T : Type} [Field k] [CommRing T]

theorem P2M_GlobalTheory_RowTriangular_eval__shift_2e105f77a3c7 [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k} (hP : RowInv r n k P)
    (σ : Ty) (i i' : Fin (r σ)) (hi : i' < i) (t : T) (y y' : Letter Ty r n → T)
    (h₁ : ∀ b, y' ⟨σ, i, b⟩ = y ⟨σ, i, b⟩ + t * y ⟨σ, i', b⟩)
    (h₂ : ∀ ℓ, (¬ ∃ b, ℓ = ⟨σ, i, b⟩) → y' ℓ = y ℓ) :
    eval₂Hom φ y' P = eval₂Hom φ y P := by sorry

alias «GlobalTheory».«RowTriangular».«eval₂_shift» := P2M_GlobalTheory_RowTriangular_eval__shift_2e105f77a3c7
