-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpComponentCombination_hC_comb_f
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination.hC_comb_f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:20.532213+00:00
-- url     : https://prove2.me/theorems/a59c05b0-b337-5091-b50a-e23ef3b6c477
-- title:
--   Perp Component Combination: h C comb f
-- statement:
--   The Perp Component Combination construction uses the h C comb f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpComponentCombination.lean#L27-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpComponentCombination.lean#L27-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpComponentCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (τ : X.Ψ) {n : ℕ} (p : ℕ) (f : Fin n → Fin r → ℂ)
  (hf : ∀ k l, hermC τ.1 X.Gm (f k) (f l) = if k = l then eps' p k else 0)
include hf

theorem ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination.hC_comb_f (y y' : Fin n → ℂ) :
    hermC τ.1 X.Gm (∑ j, y' j • f j) (∑ l, y l • f l) = ∑ j, eps' p j * (conj (y j) * y' j) := by sorry
