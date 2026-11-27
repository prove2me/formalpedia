-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ValAt_famHol
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:45:19.939589+00:00
-- url     : https://prove2.me/theorems/fbd73dc7-bc06-5a8c-8688-91ab902874ba
-- title:
--   Val At: fam Hol
-- statement:
--   The Val At construction uses the fam Hol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L101-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L101-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}
open NumberField
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (W : FamilyUnif Xo σ ty) (i : Fin W.n)
    (P : (W.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (W.Di i) ty P) (U : Xo.univ.t.G.left.Opens)
    (f : Γ(Xo.univ.t.G.left, U)) :
    IsOpen {z | ⊤ ≤ (W.ex i P z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (W.ex i P z).left U f) {z | ⊤ ≤ (W.ex i P z).left ⁻¹ᵁ U} := by sorry
