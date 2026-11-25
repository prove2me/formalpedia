-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_arc__X_isUnit_e6fe5ea1e15b
-- name    : P2M_Formalism_L2_Pj_arc__X_isUnit_e6fe5ea1e15b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:33.576269+00:00
-- url     : https://prove2.me/theorems/6c84d853-1d94-440f-88e8-b01385d9ca13
-- title:
--   P2 M Formalism L2 Pj arc  X is Unit e6fe5ea1e15b: P2 M Formalism L2 Pj arc  X is Unit e6fe5ea1e15b
-- statement:
--   The P2 M Formalism L2 Pj arc  X is Unit e6fe5ea1e15b construction uses the P2 M Formalism L2 Pj arc  X is Unit e6fe5ea1e15b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArcPtX.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArcPtX.lean#L13-L22

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArcPtX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem P2M_Formalism_L2_Pj_arc__X_isUnit_e6fe5ea1e15b (Dw : Datum H) (K₁ : Type) [Field K₁] : IsUnit (arcι Dw K₁ PowerSeries.X) := by sorry

alias «Formalism».«L2».«Pj».«arcι_X_isUnit» := P2M_Formalism_L2_Pj_arc__X_isUnit_e6fe5ea1e15b
