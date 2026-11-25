-- Prove2me | Theorems.Thm_PI_WwEvalWork_peval_Gxz
-- name    : PI.WwEvalWork.peval_Gxz
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:10.748225+00:00
-- url     : https://prove2.me/theorems/119b8aae-7d86-4914-8f4c-f79f20f072ca
-- title:
--   Ww Eval Work: peval Gxz
-- statement:
--   The Ww Eval Work construction uses the peval Gxz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L89-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionEvaluation/LsumEqOfSubset.lean#L89-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {l : ℕ} [Fact l.Prime] {N0 N1 : ℕ}

theorem PI.WwEvalWork.peval_Gxz (x : Lt × ℕ × Fin N0 → ℂ_[l]) (nu : Lt → YoungDiagram)
    (I : PI.WwEval.KM.ColChoice N1 nu) :
    peval x (PI.WwEval.KM.Gxz N0 N1 nu I) =
      MvPolynomial.aeval (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
          MvPolynomial.C (x (v.1, v.2.1, a)) * MvPolynomial.X ((v.1, a, v.2.2) : Lt × Fin N0 × Fin N1))
        (PI.WwEval.KM.nablaX N1 nu I) := by sorry
