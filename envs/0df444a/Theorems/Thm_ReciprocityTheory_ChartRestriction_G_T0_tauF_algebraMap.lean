-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_tauF_algebraMap
-- name    : ReciprocityTheory.ChartRestriction.G.T0.tauF_algebraMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:49.170418+00:00
-- url     : https://prove2.me/theorems/d9a92e78-61ef-5460-aefa-b0bcfcefdf54
-- title:
--   T0: tau F algebra Map
-- statement:
--   The T0 construction uses the tau F algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L181-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L181-L189

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.tauF_algebraMap (b : Fin (D + 1)) (u : Kˣ) (r : Ω) :
    tauF (Ω := Ω) (D := D) (N := N) b u (algebraMap Ω (OmS Ω D N) r) =
      algebraMap Ω (OmS Ω D N) r := by sorry
