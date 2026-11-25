-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_subst
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:52.103615+00:00
-- url     : https://prove2.me/theorems/1467c4df-cc58-425d-88d5-d3e30d4fd472
-- title:
--   TCPf: is Tay F subst
-- statement:
--   The TCPf construction uses the is Tay F subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L236-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L236-L269

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_subst {τ : Type} [Fintype τ] (f : (Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω f 0)
    (L : Fin 1 × Fin g → MvPowerSeries τ ℂ) (a : Fin 1 × Fin g → τ → ℂ) (hL0 : ∀ p, constantCoeff (L p) = 0)
    (hLd : ∀ p q, pderiv ℂ q (L p) = C (a p q)) :
    IsTayF f (fun q => ∑ p, a p q • (Pi.single p.2 1 : Fin g → ℂ)) (subst L (tay f 0)) := by sorry
