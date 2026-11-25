-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ExpRows_derivAt_over
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.derivAt_over
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:59.952063+00:00
-- url     : https://prove2.me/theorems/13d89d30-9668-468e-b825-4e17d02335cb
-- title:
--   Exp Rows: deriv At over
-- statement:
--   The Exp Rows construction uses the deriv At over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean#L163-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean#L163-L171

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
open AlgebraicGeometry CategoryTheory Opposite NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.derivAt_over (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left}
    (hv : IsDerivAt0 (fun z => (F.ex i P z).left) w v) :
    v ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ F.u i P := by sorry
