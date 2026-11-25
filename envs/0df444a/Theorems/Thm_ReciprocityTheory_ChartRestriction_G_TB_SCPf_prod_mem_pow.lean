-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_prod_mem_pow
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.prod_mem_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:48.876165+00:00
-- url     : https://prove2.me/theorems/a8adf873-d611-43fa-85ca-582e03826542
-- title:
--   SCPf: prod mem pow
-- statement:
--   The SCPf construction uses the prod mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SCCols.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SCCols.lean#L13-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCMain
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProdMemPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCCols
import Theorems.Thm_UpperTheory_Reformulated_B_Qk22_prod_mem_pow

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.prod_mem_pow {R k : Type} [CommRing R] [CommRing k] [Algebra R k] (J : Submodule R k) {β : Type}
    (t : Finset β) (x : β → k) (e : β → ℕ) (hx : ∀ b ∈ t, x b ∈ J ^ e b) :
    ∏ b ∈ t, x b ∈ J ^ (∑ b ∈ t, e b) := by sorry
