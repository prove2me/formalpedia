-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_Hf_eq_of_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.Hf_eq_of_pos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:23.242245+00:00
-- url     : https://prove2.me/theorems/273d4215-ca02-5ac9-897e-242740171987
-- title:
--   Majorant Normal Forms: Hf eq of pos
-- statement:
--   The Majorant Normal Forms construction uses the Hf eq of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L252-L255

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.Hf_eq_of_pos (x : Frame X.Ψ r) (τ : X.Ψ) {u : Fin r → ℂ} (hu : X.ppos x τ u = u)
    (w : Fin r → ℂ) : X.Hf x τ u w = hermC τ.1 X.Gm u w := by sorry
