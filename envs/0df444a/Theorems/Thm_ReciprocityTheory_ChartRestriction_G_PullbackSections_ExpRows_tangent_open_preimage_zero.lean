-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ExpRows_tangent_open_preimage_zero
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.tangent_open_preimage_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:35.704256+00:00
-- url     : https://prove2.me/theorems/781f7d4f-1127-5838-b1b4-e46dd5c672f5
-- title:
--   Exp Rows: tangent open preimage zero
-- statement:
--   The Exp Rows construction uses the tangent open preimage zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ExpRowsPf.lean#L62-L69

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.tangent_open_preimage_zero {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) : ⊤ ≤ (e 0) ⁻¹ᵁ U := by sorry
