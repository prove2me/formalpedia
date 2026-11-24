-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Rv_locFrame_w
-- name    : PI.ScPiBuildW.Rv.locFrame_w
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:10:42.900127+00:00
-- url     : https://prove2.me/theorems/ce54f7ea-e53c-49f0-ad3b-d1d857ce37f6
-- title:
--   Rv: loc Frame w
-- statement:
--   The Rv construction uses the loc Frame w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocFrame.lean#L72-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocFrame.lean#L72-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open PI PI.ScPiBuildW PI.ScPiBuildW.Rv
open PI.ScPiExists
variable (I : Formalism.MainNotions.S.AutInst) {r k : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
  (hn : I.n = 2 * r + k + 1) (hF : IsFrame I e f z)
  (hz : Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0) (v : InfinitePlace I.F) (w : Fin k → Fin I.n → ℂ)
  (hw : (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0)

theorem PI.ScPiBuildW.Rv.locFrame_w : (locFrame I e f z hn hF hz v w hw).w = w := by sorry

attribute [defeq] PI.ScPiBuildW.Rv.locFrame_w
