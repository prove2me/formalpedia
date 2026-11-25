-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ExpRows_dual_top_le
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.dual_top_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:51.605273+00:00
-- url     : https://prove2.me/theorems/85efde81-f2ea-4953-b2e0-2bfc45b80ea5
-- title:
--   Exp Rows: dual top le
-- statement:
--   The Exp Rows construction uses the dual top le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean#L32-L40

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.dual_top_le (W : (Spec (CommRingCat.of (DualNumber ℂ))).Opens)
    (hW : IsLocalRing.closedPoint (DualNumber ℂ) ∈ W) : ⊤ ≤ W := by sorry
