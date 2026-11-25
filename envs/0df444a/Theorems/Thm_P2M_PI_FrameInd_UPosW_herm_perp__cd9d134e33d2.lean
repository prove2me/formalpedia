-- Prove2me | Theorems.Thm_P2M_PI_FrameInd_UPosW_herm_perp__cd9d134e33d2
-- name    : P2M_PI_FrameInd_UPosW_herm_perp__cd9d134e33d2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:18.6088+00:00
-- url     : https://prove2.me/theorems/ea55c46b-901f-4eb2-94da-56e056f816cb
-- title:
--   P2 M PI Frame Ind UPos W herm perp  cd9d134e33d2: P2 M PI Frame Ind UPos W herm perp  cd9d134e33d2
-- statement:
--   The P2 M PI Frame Ind UPos W herm perp  cd9d134e33d2 construction uses the P2 M PI Frame Ind UPos W herm perp  cd9d134e33d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/ColsConjTranspose.lean#L46-L49

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

theorem P2M_PI_FrameInd_UPosW_herm_perp__cd9d134e33d2 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : v ∈ Uperp k r z z' γ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (cols k r z z' γ *ᵥ c) v = 0 := by sorry

alias «PI».«FrameInd».«UPosW».«herm_perp'» := P2M_PI_FrameInd_UPosW_herm_perp__cd9d134e33d2
