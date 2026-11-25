-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_mem_LBsub
-- name    : ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence.mem_LBsub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:42.12175+00:00
-- url     : https://prove2.me/theorems/809b4420-2df1-4d51-a14b-e85b8e79d10b
-- title:
--   Perp Basis Existence: mem LBsub
-- statement:
--   The Perp Basis Existence construction uses the mem LBsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean#L159-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean#L159-L160

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalComplementLines
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : DataX E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence.mem_LBsub {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E) (c : Fin n → E) :
    c ∈ LBsub X β ξ ↔ ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L' := by sorry
