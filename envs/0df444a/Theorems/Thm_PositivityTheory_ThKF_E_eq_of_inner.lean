-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_E_eq_of_inner
-- name    : PositivityTheory.ThKF.E.eq_of_inner
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:51:43.693798+00:00
-- url     : https://prove2.me/theorems/de3490a3-261e-4dce-a193-3ca6e9c87bd0
-- title:
--   E: eq of inner
-- statement:
--   The E construction uses the eq of inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/EqOfInner.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/EqOfInner.lean#L102-L107

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

theorem PositivityTheory.ThKF.E.eq_of_inner {u v : Sch l} (h : ∀ φ : Sch l, inner ℂ (φ.toLp 2 volume) (u.toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (v.toLp 2 volume)) : u = v := by sorry
