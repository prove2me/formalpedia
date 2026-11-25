-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalConnection_cc_jac__bcf9953926e4
-- name    : P2M_GlobalTheory_FormalConnection_cc_jac__bcf9953926e4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:25.582878+00:00
-- url     : https://prove2.me/theorems/d299cb1e-408e-46d8-9244-48a9803b3b6a
-- title:
--   P2 M Global Theory Formal Connection cc jac  bcf9953926e4: P2 M Global Theory Formal Connection cc jac  bcf9953926e4
-- statement:
--   The P2 M Global Theory Formal Connection cc jac  bcf9953926e4 construction uses the P2 M Global Theory Formal Connection cc jac  bcf9953926e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/InvariantDerivationsCommuteFormalConnection.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/InvariantDerivationsCommuteFormalConnection.lean#L147-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.FormalLog
open GlobalTheory GlobalTheory.FormalConnection
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)

theorem P2M_GlobalTheory_FormalConnection_cc_jac__bcf9953926e4 (c i : Fin d) : constantCoeff (Jac G c i) = if c = i then 1 else 0 := by sorry

alias «GlobalTheory».«FormalConnection».«cc_jac'» := P2M_GlobalTheory_FormalConnection_cc_jac__bcf9953926e4
