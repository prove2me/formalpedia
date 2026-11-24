-- Prove2me | Theorems.Thm_PI_GTS_sqAct_mem_delSq
-- name    : PI.GTS.sqAct_mem_delSq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:16.257939+00:00
-- url     : https://prove2.me/theorems/dc1225cb-04c3-4cf7-b8c7-24a8810b3bda
-- title:
--   GTS: sq Act mem del Sq
-- statement:
--   The GTS construction uses the sq Act mem del Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitPowerNormScale/NormUnitsZpowSq.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitPowerNormScale/NormUnitsZpowSq.lean#L44-L51

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

theorem PI.GTS.sqAct_mem_delSq (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ delSq ℂ N lam) : sqAct ℂ N lam g f ∈ delSq ℂ N lam := by sorry
