-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_E_toLp_rho
-- name    : PositivityTheory.ThKF.E.toLp_rho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:15.566685+00:00
-- url     : https://prove2.me/theorems/c84482ae-48bd-481e-8298-33e29917f1c9
-- title:
--   E: to Lp rho
-- statement:
--   The E construction uses the to Lp rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/EqOfInner.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/EqOfInner.lean#L97-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_EqOfInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKF.E.toLp_rho {w : l ⊕ l → ℝ} {f g : Sch l} (h : ⇑g = rhoFun w f) : g.toLp 2 volume = rho w (f.toLp 2 volume) := by sorry
