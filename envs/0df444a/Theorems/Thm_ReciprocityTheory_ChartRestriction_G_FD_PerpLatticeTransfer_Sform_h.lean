-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_Sform_h
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.Sform_h
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:05.267804+00:00
-- url     : https://prove2.me/theorems/17e8a335-1997-4c3b-9cf5-a7a1b60eca58
-- title:
--   Perp Lattice Transfer: Sform h
-- statement:
--   The Perp Lattice Transfer construction uses the Sform h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L129-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L129-L139

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

theorem ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.Sform_h (c c' : Fin n → E) :
    (Sform X β).h c c' = herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k) := by sorry
