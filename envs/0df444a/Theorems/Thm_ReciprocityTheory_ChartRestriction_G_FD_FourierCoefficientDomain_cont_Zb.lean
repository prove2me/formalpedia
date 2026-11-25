-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_cont_Zb
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_Zb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:51.607487+00:00
-- url     : https://prove2.me/theorems/6beff055-6f37-57b2-8aa5-cc6f43b7292c
-- title:
--   Fourier Coefficient Domain: cont Zb
-- statement:
--   The Fourier Coefficient Domain construction uses the cont Zb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientDomain.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientDomain.lean#L127-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_Zb {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) (y : Frame X.Ψ r) : Continuous fun t => X.Zb u (B t) y := by sorry
