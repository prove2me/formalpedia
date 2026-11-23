-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_unifOp_irreducible
-- name    : ReciprocityTheory.ChartRestriction.G.T0.unifOp_irreducible
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:16.636252+00:00
-- url     : https://prove2.me/theorems/1b9275ec-2214-499f-a56d-677a8905dcfd
-- title:
--   T0: unif Op irreducible
-- statement:
--   The T0 construction uses the unif Op irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L86-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L86-L136

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)

theorem ReciprocityTheory.ChartRestriction.G.T0.unifOp_irreducible (la : HeightOneSpectrum (𝓞 K)) : Irreducible (unifOp D N la) := by sorry
