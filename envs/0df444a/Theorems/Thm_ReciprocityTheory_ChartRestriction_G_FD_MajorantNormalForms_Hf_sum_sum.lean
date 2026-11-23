-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_Hf_sum_sum
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.Hf_sum_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:03.845489+00:00
-- url     : https://prove2.me/theorems/75123b70-08f7-4bdf-aacb-a0a4c92ab93f
-- title:
--   Majorant Normal Forms: Hf sum sum
-- statement:
--   The Majorant Normal Forms construction uses the Hf sum sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L63-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L63-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.Hf_sum_sum (x : Frame X.Ψ r) (τ : X.Ψ) (c d : Fin r → ℂ) (u w : Fin r → Fin r → ℂ) :
    X.Hf x τ (∑ a, c a • u a) (∑ b, d b • w b) =
      ∑ a, ∑ b, c a * conj (d b) * X.Hf x τ (u a) (w b) := by sorry
