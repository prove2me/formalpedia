-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AnVal_AnFr___add_7e58f427dd4e
-- name    : P2M_GlobalTheory_AnVal_AnFr___add_7e58f427dd4e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T04:40:58.951288+00:00
-- url     : https://prove2.me/theorems/cc66df9e-b53d-5c9a-bec7-96b4fc4d987c
-- title:
--   P2 M Global Theory An Val An Fr   add 7e58f427dd4e: P2 M Global Theory An Val An Fr   add 7e58f427dd4e
-- statement:
--   The P2 M Global Theory An Val An Fr   add 7e58f427dd4e construction uses the P2 M Global Theory An Val An Fr   add 7e58f427dd4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AppellHumbertFrameSemicharacter.lean#L47-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AppellHumbertFrameSemicharacter.lean#L47-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppellHumbertFrameSemicharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem P2M_GlobalTheory_AnVal_AnFr___add_7e58f427dd4e {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by sorry

alias «GlobalTheory».«AnVal».«AnFr».«χ_add» := P2M_GlobalTheory_AnVal_AnFr___add_7e58f427dd4e
