-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_ne_smul___b23005d79456
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_ne_smul___b23005d79456
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:56.608712+00:00
-- url     : https://prove2.me/theorems/2306a6f4-0c52-5075-b827-82bb99c6b325
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations ne smul   b23005d79456: P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations ne smul   b23005d79456
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations ne smul   b23005d79456 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Isotropic Combinations ne smul   b23005d79456 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L84-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L84-L94

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_ne_smul___b23005d79456 (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    {c : Fin n → E} (hc : c ≠ 0) (e e' : E) : ∑ k, c k • β k + e • ξ ≠ e' • ξ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«IsotropicCombinations».«ne_smul_ξ» := P2M_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_ne_smul___b23005d79456
