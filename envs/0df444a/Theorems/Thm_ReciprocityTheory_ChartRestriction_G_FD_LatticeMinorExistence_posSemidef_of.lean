-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_posSemidef_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.posSemidef_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:10.33853+00:00
-- url     : https://prove2.me/theorems/7f130d6d-fdd4-4fa3-baec-37f5611aa84c
-- title:
--   Lattice Minor Existence: pos Semidef of
-- statement:
--   The Lattice Minor Existence construction uses the pos Semidef of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeMinorExistence.lean#L92-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeMinorExistence.lean#L92-L113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.posSemidef_of {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} (hχ : IsHermFam χ) (τ0 : X.Ψ)
    (h : ∀ x : Fin 2 → ℂ, x ≠ 0 → 0 ≤ (∑ i, ∑ k, χ τ0 i k * conj (x i) * x k).re) :
    (Matrix.of (χ τ0)).PosSemidef := by sorry
