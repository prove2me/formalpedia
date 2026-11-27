-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_isotropicCoefficientSplitting_holds
-- name    : ReciprocityTheory.ChartRestriction.G.FD.isotropicCoefficientSplitting_holds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:16:16.389313+00:00
-- url     : https://prove2.me/theorems/8aeec2da-d7e0-4faf-a424-b3a8a868ffb3
-- title:
--   FD: isotropic Coefficient Splitting holds
-- statement:
--   The FD construction uses the isotropic Coefficient Splitting holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCoefficientLemmas.lean#L61-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCoefficientLemmas.lean#L61-L119

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open IsotropicCoefficientLemmas

theorem ReciprocityTheory.ChartRestriction.G.FD.isotropicCoefficientSplitting_holds : IsotropicCoefficientSplitting (E := E) := by sorry
