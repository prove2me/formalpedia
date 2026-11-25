-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_LB_selfDual
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.LB_selfDual
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:35.578836+00:00
-- url     : https://prove2.me/theorems/11b9f646-971c-5828-87a7-33d05db15539
-- title:
--   Perp Lattice Transfer: LB self Dual
-- statement:
--   The Perp Lattice Transfer construction uses the LB self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L187-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L187-L208

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

theorem ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.LB_selfDual (hξ : X.IsIso ξ) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin n → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    ReciprocityTheory.MultiplicativeHeights.IsSelfDual (Sform X β) (LBsub X β ξ) := by sorry
