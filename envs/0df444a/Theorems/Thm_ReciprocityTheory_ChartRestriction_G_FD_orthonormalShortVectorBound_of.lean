-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_orthonormalShortVectorBound_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.orthonormalShortVectorBound_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:47.537594+00:00
-- url     : https://prove2.me/theorems/2d1159d5-503b-52dd-be34-161869e981f0
-- title:
--   FD: orthonormal Short Vector Bound of
-- statement:
--   The FD construction uses the orthonormal Short Vector Bound of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthonormalShortVectorBoundOf.lean#L108-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthonormalShortVectorBoundOf.lean#L108-L167

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ReducedLatticeShortBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramSchmidtEigenframe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryFixingIsotropicPlane
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalShortVectorBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.orthonormalShortVectorBound_of (hD4 : ShortVectorBound (E := E)) (hD5 : CoveringRadiusStatement) : OrthonormalShortVectorBound (E := E) := by sorry
