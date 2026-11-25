-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RowTriangular_eval__unip_450ff3a92c12
-- name    : P2M_GlobalTheory_RowTriangular_eval__unip_450ff3a92c12
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:00.73144+00:00
-- url     : https://prove2.me/theorems/1705fd00-3dc8-4394-b759-57fb96943a72
-- title:
--   P2 M Global Theory Row Triangular eval  unip 450ff3a92c12: P2 M Global Theory Row Triangular eval  unip 450ff3a92c12
-- statement:
--   The P2 M Global Theory Row Triangular eval  unip 450ff3a92c12 construction uses the P2 M Global Theory Row Triangular eval  unip 450ff3a92c12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/InvariantOperatorValueTriangularChange.lean#L132-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/InvariantOperatorValueTriangularChange.lean#L132-L138

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

theorem P2M_GlobalTheory_RowTriangular_eval__unip_450ff3a92c12 [Infinite k] [Fintype Ty] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (N : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hN : ∀ σ i j, i ≤ j → N σ i j = 0)
    (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => y ℓ + ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) P = eval₂Hom φ y P := by sorry

alias «GlobalTheory».«RowTriangular».«eval₂_unip» := P2M_GlobalTheory_RowTriangular_eval__unip_450ff3a92c12
