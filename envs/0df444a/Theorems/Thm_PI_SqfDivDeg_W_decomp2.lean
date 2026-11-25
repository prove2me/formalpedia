-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_decomp2
-- name    : PI.SqfDivDeg.W.decomp2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:25:07.376916+00:00
-- url     : https://prove2.me/theorems/de329413-8663-4699-bac7-739f13739ec5
-- title:
--   W: decomp2
-- statement:
--   The W construction uses the decomp2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/CardMonicTwoRootsLe.lean#L39-L49

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical

theorem PI.SqfDivDeg.W.decomp2 {g : ℕ} [Fact g.Prime] {f : (ZMod g)[X]} {c d : ZMod g} (hcd : c ≠ d)
    (hc : f.IsRoot c) (hd : f.IsRoot d) :
    (X - C c) * ((X - C d) * ((f /ₘ (X - C c)) /ₘ (X - C d))) = f := by sorry
