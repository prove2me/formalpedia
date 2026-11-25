-- Prove2me | Theorems.Thm_PI_GTS_re_normFock_smul
-- name    : PI.GTS.re_normFock_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:21.63642+00:00
-- url     : https://prove2.me/theorems/f1e19e5e-6f6f-4cbc-9429-5506a81ae9ea
-- title:
--   GTS: re norm Fock smul
-- statement:
--   The GTS construction uses the re norm Fock smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitPowerNormScale/NormUnitsZpowSq.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitPowerNormScale/NormUnitsZpowSq.lean#L29-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTS
open Formalism.BasicNotions MvPolynomial

theorem PI.GTS.re_normFock_smul {N : ℕ} (lam : DomWeight N) (c : ℂ) (x : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam (c • x) (c • x)).re = ‖c‖ ^ 2 * (normFock lam x x).re := by sorry
