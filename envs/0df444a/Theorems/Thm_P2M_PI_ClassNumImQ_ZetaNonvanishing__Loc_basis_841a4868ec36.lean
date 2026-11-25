-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_basis_841a4868ec36
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_basis_841a4868ec36
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:44:08.720036+00:00
-- url     : https://prove2.me/theorems/17bdf7fa-e050-43d8-97c8-aab58744e884
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  Loc basis 841a4868ec36: P2 M PI Class Num Im Q Zeta Nonvanishing  Loc basis 841a4868ec36
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  Loc basis 841a4868ec36 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  Loc basis 841a4868ec36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/LocOdd.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/LocOdd.lean#L18-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ClassNumImQInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_LocOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂ PI.ClassNumImQ.ZetaNonvanishing₂.Loc
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_basis_841a4868ec36 (hq : QuadData d K b) (x : 𝓞 K) : ∃ m n : ℤ, x = m + n * om hq := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«Loc».«basis» := P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_basis_841a4868ec36
