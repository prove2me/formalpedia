-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_Tmap_inj
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.Tmap_inj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:00.557739+00:00
-- url     : https://prove2.me/theorems/d1892f7d-1d0e-419a-a1b0-da4352304c07
-- title:
--   Perp Lattice Transfer: Tmap inj
-- statement:
--   The Perp Lattice Transfer construction uses the Tmap inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L47-L64

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

theorem ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.Tmap_inj (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E)) :
    Function.Injective (Tmap β ξ) := by sorry
