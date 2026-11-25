-- Prove2me | Theorems.Thm_PI_GTS_fockF_smul_self
-- name    : PI.GTS.fockF_smul_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:16.303654+00:00
-- url     : https://prove2.me/theorems/1af39842-c23a-5ca4-8375-154da804ccd1
-- title:
--   GTS: fock F smul self
-- statement:
--   The GTS construction uses the fock F smul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitPowerNormScale/NormUnitsZpowSq.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitPowerNormScale/NormUnitsZpowSq.lean#L21-L27

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

theorem PI.GTS.fockF_smul_self {σ : Type*} (c : ℂ) (f : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) (c • f) = (c * star c) * Formalism.REAL.fockF f f := by sorry
