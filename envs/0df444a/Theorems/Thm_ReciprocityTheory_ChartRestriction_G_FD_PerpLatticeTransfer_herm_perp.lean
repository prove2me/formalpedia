-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_herm_perp
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.herm_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:35.895657+00:00
-- url     : https://prove2.me/theorems/8470f316-16c2-4114-ba19-a34ad249b273
-- title:
--   Perp Lattice Transfer: herm perp
-- statement:
--   The Perp Lattice Transfer construction uses the herm perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L141-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)

theorem ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.herm_perp (hβξ : ∀ k, herm X.Gm (β k) ξ = 0) (c : Fin n → E) :
    herm X.Gm (∑ k, c k • β k) ξ = 0 := by sorry
