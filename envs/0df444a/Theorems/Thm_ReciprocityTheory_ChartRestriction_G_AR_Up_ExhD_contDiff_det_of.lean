-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhD_contDiff_det_of
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD.contDiff_det_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:00.91162+00:00
-- url     : https://prove2.me/theorems/76fba572-6154-5745-880b-c477aa53e679
-- title:
--   Exh D: cont Diff det of
-- statement:
--   The Exh D construction uses the cont Diff det of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfB.lean#L151-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfB.lean#L151-L158

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
variable {f p q N' : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD.contDiff_det_of {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {m : ℕ} {M : E → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun x => M x i j) : ContDiff 𝕜 ∞ fun x => (M x).det := by sorry
