-- Prove2me | Theorems.Thm_PI_WGB_torus_mem_B
-- name    : PI.WGB.torus_mem_B
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:46:04.961031+00:00
-- url     : https://prove2.me/theorems/e45f1f81-3612-4144-9473-0144e5937d39
-- title:
--   WGB: torus mem B
-- statement:
--   The WGB construction uses the torus mem B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L189-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L189-L197

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial

theorem PI.WGB.torus_mem_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (t : Fin n → ℂˣ) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ))) f ∈ W := by sorry
