-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__frame_inv_c135116a64e8
-- name    : P2M_PI_MirrorSection__frame_inv_c135116a64e8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:39.5758+00:00
-- url     : https://prove2.me/theorems/39f655d8-ae96-46c4-a201-39f2e2cd7866
-- title:
--   P2 M PI Mirror Section  frame inv c135116a64e8: P2 M PI Mirror Section  frame inv c135116a64e8
-- statement:
--   The P2 M PI Mirror Section  frame inv c135116a64e8 construction uses the P2 M PI Mirror Section  frame inv c135116a64e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/MirrorDecompOf.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/MirrorDecompOf.lean#L17-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_MirrorDecompOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem P2M_PI_MirrorSection__frame_inv_c135116a64e8 {s : Matrix n n ℂ} {x : Matrix m m ℂ} {F : Matrix n m ℂ}
    (hs : IsUnit s.det) (hx : IsUnit x.det) (h : s * F = F * x) : s⁻¹ * F = F * x⁻¹ := by sorry

alias «PI».«MirrorSection₂».«frame_inv» := P2M_PI_MirrorSection__frame_inv_c135116a64e8
