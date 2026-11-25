-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_B___01ead02708b4
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_B___01ead02708b4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:05.486865+00:00
-- url     : https://prove2.me/theorems/a18dca50-efae-4bba-8bc9-6008996cd8c1
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations herm B   01ead02708b4: P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations herm B   01ead02708b4
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations herm B   01ead02708b4 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations herm B   01ead02708b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L38-L40

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
variable {n : ℕ} (G : Matrix (Fin r) (Fin r) E)
variable {G} (hG : ∀ a b, cc (G a b) = G b a) {ξ : Fin r → E} {β : Fin n → Fin r → E}
  (hβ : ∀ k, herm G (β k) ξ = 0) (hξξ : herm G ξ ξ = 0)
include hβ

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_B___01ead02708b4 (c : Fin n → E) : herm G (∑ k, c k • β k) ξ = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«IsotropicCombinations».«herm_B_ξ» := P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_B___01ead02708b4
