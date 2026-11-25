-- Prove2me | Theorems.Thm_PI_SqfDivDeg_W_second_pair
-- name    : PI.SqfDivDeg.W.second_pair
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:25:06.475673+00:00
-- url     : https://prove2.me/theorems/de49edce-b847-452e-bc6a-fe14728914f6
-- title:
--   W: second pair
-- statement:
--   The W construction uses the second pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/FibreNonempty.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/FibreNonempty.lean#L9-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_FibreNonempty
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

theorem PI.SqfDivDeg.W.second_pair {g : ℕ} [Fact g.Prime] {q h : (ZMod g)[X]} (hq : q.Monic) (hh : h.Monic)
    (hs : Squarefree (q * h)) {x y : ZMod g} (hx : q.IsRoot x) (hy : h.IsRoot y) :
    ((X - C y) * (q /ₘ (X - C x))).Monic ∧ ((X - C x) * (h /ₘ (X - C y))).Monic ∧
    ((X - C y) * (q /ₘ (X - C x))).natDegree = q.natDegree ∧
    ((X - C x) * (h /ₘ (X - C y))).natDegree = h.natDegree ∧
    ((X - C y) * (q /ₘ (X - C x))) * ((X - C x) * (h /ₘ (X - C y))) = q * h ∧
    (X - C y) * (q /ₘ (X - C x)) ≠ q := by sorry
