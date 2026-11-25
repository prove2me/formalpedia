-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInv_quadPoly_irreducible
-- name    : PI.UnitaryGroupMassFormula.ClassNumImQInv.quadPoly_irreducible
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:21.155509+00:00
-- url     : https://prove2.me/theorems/a71d74e8-7d5f-4be9-b920-7c5bbbbe16f5
-- title:
--   Class Num Im QInv: quad Poly irreducible
-- statement:
--   The Class Num Im QInv construction uses the quad Poly irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticInvariants/QuadPolyIrreducible.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticInvariants/QuadPolyIrreducible.lean#L34-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ClassNumImQInv
open PI.ClassNumImQ
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}

theorem PI.UnitaryGroupMassFormula.ClassNumImQInv.quadPoly_irreducible (hq : QuadData d K b) : Irreducible (quadPoly d) := by sorry
