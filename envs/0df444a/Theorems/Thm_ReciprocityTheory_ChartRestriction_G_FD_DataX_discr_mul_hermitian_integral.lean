-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_discr_mul_hermitian_integral
-- name    : ReciprocityTheory.ChartRestriction.G.FD.DataX.discr_mul_hermitian_integral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:51.458558+00:00
-- url     : https://prove2.me/theorems/9e3bf9e1-862e-4079-8866-2b8ee69d188e
-- title:
--   Data X: discr mul hermitian integral
-- statement:
--   The Data X construction uses the discr mul hermitian integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L30-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.DataX.discr_mul_hermitian_integral {v w : Fin r → E} (hv : v ∈ X.Λ) (hw : w ∈ X.Λ) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * (X.ξ0 * herm X.Gm v w)) := by sorry
