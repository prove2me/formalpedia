-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_flow_coefficient_decay_holds
-- name    : ReciprocityTheory.ChartRestriction.G.FD.flow_coefficient_decay_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:57.402852+00:00
-- url     : https://prove2.me/theorems/186ed60e-e5a3-5849-aece-78a74794f645
-- title:
--   FD: flow coefficient decay holds
-- statement:
--   The FD construction uses the flow coefficient decay holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowCoefficientDecayHolds.lean#L11-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowCoefficientDecayHolds.lean#L11-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecayHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.flow_coefficient_decay_holds (h1 : UnipotentVectorGroup (E := E)) (h2 : UnipotentLatticeLift (E := E))
    (h3 : FourierCoefficientProperties (E := E)) (h3d : FourierCoefficientSupport (E := E)) (h4 : HolomorphicPeriodicityExtension (E := E)) :
    FlowCoefficientDecay (E := E) := by sorry
