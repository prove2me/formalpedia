-- Prove2me | Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_bcG_smulR
-- name    : PI.LocLatSat.UnitaryGroupMassFormula.bcG_smulR
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:34:55.645148+00:00
-- url     : https://prove2.me/theorems/923793f1-81f9-55d0-b6c2-b64e19afa3c6
-- title:
--   Unitary Group Mass Formula: bc G smul R
-- statement:
--   The Unitary Group Mass Formula construction uses the bc G smul R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeSaturation/BcGSmulR.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeSaturation/BcGSmulR.lean#L40-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open PI PI.LocLatSat PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
omit [IsDedekindDomain R] [IsFractionRing R K]

theorem PI.LocLatSat.UnitaryGroupMassFormula.bcG_smulR (r : R) (x : Fin n → K) : bcG φ (r • x) = φ (algebraMap R K r) • bcG φ x := by sorry
