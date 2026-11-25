-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_isHermFam_real_linear_comb
-- name    : ReciprocityTheory.ChartRestriction.G.FD.isHermFam_real_linear_comb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:45.507819+00:00
-- url     : https://prove2.me/theorems/9ca2a509-e6cf-5f0a-ac71-f7e696ef82cc
-- title:
--   FD: is Herm Fam real linear comb
-- statement:
--   The FD construction uses the is Herm Fam real linear comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientSupportHolds.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientSupportHolds.lean#L17-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodLatticeCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientsOfVectorGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentLatticeLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.isHermFam_real_linear_comb {r : ℕ} (X : Data E r) (g N : ℕ) (ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ)
    (hω : ∀ j, ω j ∈ X.LZ g) (t : Fin N → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by sorry
