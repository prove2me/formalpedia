-- Prove2me | Theorems.Thm_PI_ET_HornW_exp_conj
-- name    : PI.ET.HornW.exp_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:41.685932+00:00
-- url     : https://prove2.me/theorems/b9dfc71d-6f59-54b4-8098-503cec05856b
-- title:
--   Horn W: exp conj
-- statement:
--   The Horn W construction uses the exp conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L40-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}

theorem PI.ET.HornW.exp_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) :
    NormedSpace.exp (W * diagonal (fun i => (d i : ℂ)) * Wᴴ) =
      W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ := by sorry
