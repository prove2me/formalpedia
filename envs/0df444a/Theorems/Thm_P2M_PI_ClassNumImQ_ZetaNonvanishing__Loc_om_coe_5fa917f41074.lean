-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_om_coe_5fa917f41074
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_om_coe_5fa917f41074
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:50.886341+00:00
-- url     : https://prove2.me/theorems/78028202-110b-5483-bf20-bc27afc8fc70
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  Loc om coe 5fa917f41074: P2 M PI Class Num Im Q Zeta Nonvanishing  Loc om coe 5fa917f41074
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  Loc om coe 5fa917f41074 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  Loc om coe 5fa917f41074 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/LocOdd.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/LocOdd.lean#L16-L16

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_om_coe_5fa917f41074 (hq : QuadData d K b) : ((om hq : 𝓞 K) : K) = (1 + b) / 2 := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«Loc».«om_coe» := P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_om_coe_5fa917f41074
