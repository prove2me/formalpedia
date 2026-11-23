-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_hC_comb2_ortho
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:26:02.694095+00:00
-- url     : https://prove2.me/theorems/b968078b-008a-40ad-b40e-08197cc38c79
-- title:
--   Isotropic Combinations: h C comb2 ortho
-- statement:
--   The Isotropic Combinations construction uses the h C comb2 ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L127-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L127-L154

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCombinations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n p : ℕ} (f : Fin n → Fin r → ℂ)
    (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (b c : Fin n → ℂ) :
    hermC τ G (∑ k, b k • f k) (∑ l, c l • f l) = ReciprocityTheory.MultiplicativeHeights.jForm p c b := by sorry
