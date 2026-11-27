-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicThreshold_iso_threshold
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold.iso_threshold
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:27.310054+00:00
-- url     : https://prove2.me/theorems/f2a005b4-5aec-44c4-a87c-fab2cf81513e
-- title:
--   Isotropic Threshold: iso threshold
-- statement:
--   The Isotropic Threshold construction uses the iso threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicThreshold.lean#L18-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicThreshold.lean#L18-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicThreshold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold.iso_threshold (X : Data E r) : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ x ∈ X.dom, ∀ v ∈ X.Λ,
    ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) < δ0 → herm X.Gm v v = 0 := by sorry
