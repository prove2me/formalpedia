-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_algK_unif
-- name    : ReciprocityTheory.ChartRestriction.G.T0.algK_unif
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:25.798229+00:00
-- url     : https://prove2.me/theorems/7341b770-ffeb-41c9-8f8c-4dd03f1de0e9
-- title:
--   T0: alg K unif
-- statement:
--   The T0 construction uses the alg K unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean#L138-L141

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

theorem ReciprocityTheory.ChartRestriction.G.T0.algK_unif (la : HeightOneSpectrum (𝓞 K)) :
    algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) = OpToKT D N la (unifOp D N la) := by sorry
