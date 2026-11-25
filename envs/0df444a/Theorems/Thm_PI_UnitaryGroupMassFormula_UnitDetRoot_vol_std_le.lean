-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_vol_std_le
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.vol_std_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:40.381991+00:00
-- url     : https://prove2.me/theorems/2f586a9f-ada0-4be6-a09c-fdfe1196bb61
-- title:
--   Unit Det Root: vol std le
-- statement:
--   The Unit Det Root construction uses the vol std le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean#L79-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean#L79-L104

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.vol_std_le {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    (hok : UnitDetRootDefs.CmOK a b c d) {m : Type} [Fintype m] [DecidableEq m] :
    vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≤ Submodule.span (𝓞 (KF b d)) {lam ^ Fintype.card m} := by sorry
