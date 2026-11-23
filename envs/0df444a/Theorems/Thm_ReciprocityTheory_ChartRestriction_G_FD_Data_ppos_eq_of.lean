-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_eq_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:35.349666+00:00
-- url     : https://prove2.me/theorems/d4f80086-282a-4337-8e8e-dbf9aab6bac5
-- title:
--   Data: ppos eq of
-- statement:
--   The Data construction uses the ppos eq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatMulVec.lean#L77-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatMulVec.lean#L77-L95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_eq_of (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (β : Fin X.p0 → ℂ)
    (horth : ∀ b : Fin X.p0, hermC τ.1 X.Gm (u - ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) :
    X.ppos x τ u = ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a) := by sorry
