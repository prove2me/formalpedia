-- Prove2me | Theorems.Thm_PIW_AdelClassFin_hmk_int
-- name    : PIW.AdelClassFin.hmk_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:12.668902+00:00
-- url     : https://prove2.me/theorems/88af7ce6-5bfb-4b31-849d-37da33e6fe5b
-- title:
--   Adel Class Fin: hmk int
-- statement:
--   The Adel Class Fin construction uses the hmk int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HmkFactor.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HmkFactor.lean#L21-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HmkFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open MeasureTheory Matrix Module
open scoped MatrixOrder

theorem PIW.AdelClassFin.hmk_int {N : ℕ} (x : Fin N → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin N)))) :
    ∃ c : Fin N → ℤ, (fun i => (c i : ℝ)) = x := by sorry
