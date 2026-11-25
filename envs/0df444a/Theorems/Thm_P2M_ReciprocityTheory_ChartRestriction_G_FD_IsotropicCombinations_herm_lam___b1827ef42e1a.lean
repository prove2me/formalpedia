-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_lam___b1827ef42e1a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_lam___b1827ef42e1a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:02.781195+00:00
-- url     : https://prove2.me/theorems/a9b19182-85c2-5f34-bac3-6d520e8fe847
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations herm lam   b1827ef42e1a: P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations herm lam   b1827ef42e1a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations herm lam   b1827ef42e1a construction uses the P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations herm lam   b1827ef42e1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L43-L45

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
include hβ hξξ

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_lam___b1827ef42e1a (c : Fin n → E) (e : E) : herm G (∑ k, c k • β k + e • ξ) ξ = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«IsotropicCombinations».«herm_lam_ξ» := P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_lam___b1827ef42e1a
