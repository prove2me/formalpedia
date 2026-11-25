-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_lam_lam
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.herm_lam_lam
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:50.537022+00:00
-- url     : https://prove2.me/theorems/7c3dc568-5fb6-52dd-8565-a5c93689db24
-- title:
--   Isotropic Combinations: herm lam lam
-- statement:
--   The Isotropic Combinations construction uses the herm lam lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L48-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L48-L82

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
include hG hβ hξξ

theorem ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.herm_lam_lam (c c' : Fin n → E) (e e' : E) :
    herm G (∑ k, c k • β k + e • ξ) (∑ k, c' k • β k + e' • ξ) =
      herm G (∑ k, c k • β k) (∑ k, c' k • β k) := by sorry
