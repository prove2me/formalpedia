-- Prove2me | Theorems.Thm_PI_WeylForKInhab_diag_mem
-- name    : PI.WeylForKInhab.diag_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:20.929434+00:00
-- url     : https://prove2.me/theorems/3aa32087-5c63-4343-9d09-dc2f2f863461
-- title:
--   Weyl For KInhab: diag mem
-- statement:
--   The Weyl For KInhab construction uses the diag mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/TrivKtype.lean#L11-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/TrivKtype.lean#L11-L29

import Definitions.Def_Formalism_PeriodIntegrals_WeylForK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UpqRep Matrix
noncomputable section
open PI PI.WeylForKInhab

theorem PI.WeylForKInhab.diag_mem {N : ℕ} (ε : Fin N → Bool) (θ : Fin N → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by sorry
