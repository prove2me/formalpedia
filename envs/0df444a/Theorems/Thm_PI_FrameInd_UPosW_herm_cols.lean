-- Prove2me | Theorems.Thm_PI_FrameInd_UPosW_herm_cols
-- name    : PI.FrameInd.UPosW.herm_cols
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:31:12.474831+00:00
-- url     : https://prove2.me/theorems/366754e2-288e-4ec6-9360-c1182778310f
-- title:
--   UPos W: herm cols
-- statement:
--   The UPos W construction uses the herm cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L27-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_ColsConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd PI.FrameInd.UPosW

theorem PI.FrameInd.UPosW.herm_cols (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (cols k r z z' γ *ᵥ c) (cols k r z z' γ *ᵥ c) = star c ⬝ᵥ (gramM k r z z' γ *ᵥ c) := by sorry
