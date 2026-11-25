-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_chiOf_inj
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices.chiOf_inj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:02.094176+00:00
-- url     : https://prove2.me/theorems/ba8d66e3-fa60-586c-b3b5-3a38525f6690
-- title:
--   Fourier Coefficient Matrices: chi Of inj
-- statement:
--   The Fourier Coefficient Matrices construction uses the chi Of inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientMatrices.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientMatrices.lean#L206-L209

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)
variable (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) (hN : N = 4 * Fintype.card ι)

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices.chiOf_inj : Function.Injective (chiOf ω hω hli hN) := by sorry
