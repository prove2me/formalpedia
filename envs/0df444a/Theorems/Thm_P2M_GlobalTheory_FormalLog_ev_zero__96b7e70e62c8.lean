-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalLog_ev_zero__96b7e70e62c8
-- name    : P2M_GlobalTheory_FormalLog_ev_zero__96b7e70e62c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:22.524983+00:00
-- url     : https://prove2.me/theorems/52fb10f7-5959-487e-90d0-a03bddc83869
-- title:
--   P2 M Global Theory Formal Log ev zero  96b7e70e62c8: P2 M Global Theory Formal Log ev zero  96b7e70e62c8
-- statement:
--   The P2 M Global Theory Formal Log ev zero  96b7e70e62c8 construction uses the P2 M Global Theory Formal Log ev zero  96b7e70e62c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffEv.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffEv.lean#L50-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d m n : ℕ}

theorem P2M_GlobalTheory_FormalLog_ev_zero__96b7e70e62c8 {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by sorry

alias «GlobalTheory».«FormalLog».«ev_zero'» := P2M_GlobalTheory_FormalLog_ev_zero__96b7e70e62c8
