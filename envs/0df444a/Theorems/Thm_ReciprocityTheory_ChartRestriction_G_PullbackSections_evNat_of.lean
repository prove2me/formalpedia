-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_evNat_of
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:33:50.049114+00:00
-- url     : https://prove2.me/theorems/b7fa15af-7fdc-56c2-8c20-9e042e42f838
-- title:
--   Pullback Sections: ev Nat of
-- statement:
--   The Pullback Sections construction uses the ev Nat of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/EvNatPf.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/EvNatPf.lean#L19-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IndepPts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_EvNatPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : AllTest Xo c) : EvNat Xo c := by sorry
