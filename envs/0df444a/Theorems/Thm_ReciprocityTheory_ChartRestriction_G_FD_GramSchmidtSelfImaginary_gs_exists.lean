-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_gs_exists
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.gs_exists
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:10.708931+00:00
-- url     : https://prove2.me/theorems/37092732-0084-5220-9503-970706610226
-- title:
--   Gram Schmidt Self Imaginary: gs exists
-- statement:
--   The Gram Schmidt Self Imaginary construction uses the gs exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L94-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpSpanRight.lean#L94-L341

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable (hG : ∀ a b, cc (G a b) = G b a)
include hG

theorem ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.gs_exists {n : ℕ} (p : ℕ) (Y : Fin n → Fin r → ℂ) (hind : LinearIndependent ℂ Y)
    (horth : ∀ j k : Fin n, (j : ℕ) < p → p ≤ (k : ℕ) → hermC τ G (Y j) (Y k) = 0)
    (hpos : ∀ w : Fin n → ℂ, (∀ j : Fin n, p ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
      0 < (hermC τ G (∑ j, w j • Y j) (∑ j, w j • Y j)).re)
    (hneg : ∀ w : Fin n → ℂ, (∀ j : Fin n, (j : ℕ) < p → w j = 0) → w ≠ 0 →
      (hermC τ G (∑ j, w j • Y j) (∑ j, w j • Y j)).re < 0) :
    ∃ g : Fin n → Fin r → ℂ,
      (∀ c a : Fin n, hermC τ G (g c) (g a) =
        if c = a then (if (c : ℕ) < p then 1 else -1) else 0) ∧
      (∀ c : Fin n, (c : ℕ) < p → g c ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) < p})) ∧
      (∀ c : Fin n, g c ∈ Submodule.span ℂ (Set.range Y)) ∧
      (∀ j : Fin n, ∃ β : Fin n → ℂ, (∀ c : Fin n, ¬((c : ℕ) < p ↔ (j : ℕ) < p) → β c = 0) ∧
        Y j = ∑ c, β c • g c) := by sorry
