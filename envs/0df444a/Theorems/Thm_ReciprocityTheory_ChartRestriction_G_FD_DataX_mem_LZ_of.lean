-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_mem_LZ_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.DataX.mem_LZ_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:27.641024+00:00
-- url     : https://prove2.me/theorems/493c45fb-c2a3-4419-9ec5-8e11e3798ae0
-- title:
--   Data X: mem LZ of
-- statement:
--   The Data X construction uses the mem LZ of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L133-L139

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

theorem ReciprocityTheory.ChartRestriction.G.FD.DataX.mem_LZ_of (w : Fin 2 → Fin 2 → E) (hwi : ∀ i k, IsIntegral ℤ (w i k))
    (hwh : ∀ i k, cc (w i k) = w k i) :
    X.embH (Matrix.of fun i k => X.c0E * w i k) ∈ X.LZ X.g := by sorry
