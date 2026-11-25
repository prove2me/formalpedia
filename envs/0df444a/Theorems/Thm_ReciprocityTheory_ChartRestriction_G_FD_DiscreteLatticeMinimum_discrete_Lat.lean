-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscreteLatticeMinimum_discrete_Lat
-- name    : ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum.discrete_Lat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:23:57.360885+00:00
-- url     : https://prove2.me/theorems/11ef600d-d84c-5c64-89b1-3315db16e970
-- title:
--   Discrete Lattice Minimum: discrete Lat
-- statement:
--   The Discrete Lattice Minimum construction uses the discrete Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscreteLatticeMinimum.lean#L149-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscreteLatticeMinimum.lean#L149-L165

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]
variable {ξ} (hξ : Y.IsIso ξ)
variable (ep0 : ℝ) (hns : ∀ x ∈ Y.L', herm Y.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : Y.Ψ, ep0 ≤ Y.maj z τ (Y.ucomp z ξ (Y.embV x) τ))
include hns

theorem ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum.discrete_Lat (hep : 0 < ep0) : DiscreteTopology (Lat z ξ hξ) := by sorry
