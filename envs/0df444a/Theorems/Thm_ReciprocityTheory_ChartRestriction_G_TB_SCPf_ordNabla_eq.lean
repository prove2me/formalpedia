-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_ordNabla_eq
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.ordNabla_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:46.836855+00:00
-- url     : https://prove2.me/theorems/fab0df43-161b-424c-a62f-6eced8a493dd
-- title:
--   SCPf: ord Nabla eq
-- statement:
--   The SCPf construction uses the ord Nabla eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXHasSubst.lean#L157-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXHasSubst.lean#L157-L199

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
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
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.ordNabla_eq (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (hc : ∀ l l', s l = s l' → Commute (nablaL B h m (ξ l).1 (ξ l).2) (nablaL B h m (ξ l').1 (ξ l').2))
    (P : MvPolynomial ι k) (G : AA k d) :
    ordNabla k B h m s ξ P G =
      PI.WickFormula.ordEval (opL B h m s ξ) (opR B h m s ξ) (MvPolynomial.rename (sideE s) P) G := by sorry
