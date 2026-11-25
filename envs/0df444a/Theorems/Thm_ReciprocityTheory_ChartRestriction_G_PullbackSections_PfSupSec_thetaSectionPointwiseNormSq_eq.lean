-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_PfSupSec_thetaSectionPointwiseNormSq_eq
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec.thetaSectionPointwiseNormSq_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:32.148034+00:00
-- url     : https://prove2.me/theorems/49881662-046a-4316-8a20-727c205aa9e8
-- title:
--   Pf Sup Sec: theta Section Pointwise Norm Sq eq
-- statement:
--   The Pf Sup Sec construction uses the theta Section Pointwise Norm Sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SupSec.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SupSec.lean#L35-L45

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec.thetaSectionPointwiseNormSq_eq (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (w : Fin 1 → Vsp X.dim) :
    X.ptN2 1 s w = (toGT X).ptN2 1 (fun v => s (fun _ => v)) (w 0) := by sorry
