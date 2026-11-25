-- Prove2me | Theorems.Thm_PI_ET_HornW_sq_conj
-- name    : PI.ET.HornW.sq_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:48.803946+00:00
-- url     : https://prove2.me/theorems/8de1ec50-3a77-4647-89ec-50cb7661688d
-- title:
--   Horn W: sq conj
-- statement:
--   The Horn W construction uses the sq conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L51-L58

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

theorem PI.ET.HornW.sq_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) :
    (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ) *
        (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ) =
      W * diagonal (fun i => (Real.exp (2 * d i) : ℂ)) * Wᴴ := by sorry
