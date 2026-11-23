-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_PfSupSec_symmetricMeasure_l2Norm_eq_resolutionL2
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec.symmetricMeasure_l2Norm_eq_resolutionL2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:51.137963+00:00
-- url     : https://prove2.me/theorems/c836bab9-76f7-4922-b5d4-21c567722695
-- title:
--   Pf Sup Sec: symmetric Measure l2 Norm eq resolution L2
-- statement:
--   The Pf Sup Sec construction uses the symmetric Measure l2 Norm eq resolution L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SupSec.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SupSec.lean#L47-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_SupGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExtProof
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SupSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
open NumberField ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec.symmetricMeasure_l2Norm_eq_resolutionL2 (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 1 s = (toGT X).l2 1 (fun v => s (fun _ => v)) := by sorry
