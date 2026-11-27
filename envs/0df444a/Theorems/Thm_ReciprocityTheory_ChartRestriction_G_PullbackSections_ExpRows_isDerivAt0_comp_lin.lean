-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ExpRows_isDerivAt0_comp_lin
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_lin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T18:16:24.043778+00:00
-- url     : https://prove2.me/theorems/cc877086-8bd7-5f9e-b6ff-f01b05afb68c
-- title:
--   Exp Rows: is Deriv At0 comp lin
-- statement:
--   The Exp Rows construction uses the is Deriv At0 comp lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean#L134-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean#L134-L146

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
variable {g : ℕ} {Y : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_lin {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (hol : IsHolFam e) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e (D w) v) :
    IsDerivAt0 (fun z => e (D z)) w v := by sorry
