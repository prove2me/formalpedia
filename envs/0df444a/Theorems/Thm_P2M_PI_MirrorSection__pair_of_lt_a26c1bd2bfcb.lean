-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__pair_of_lt_a26c1bd2bfcb
-- name    : P2M_PI_MirrorSection__pair_of_lt_a26c1bd2bfcb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:58:03.143893+00:00
-- url     : https://prove2.me/theorems/62705a2e-0bf0-4d04-b52c-22198159e4b0
-- title:
--   P2 M PI Mirror Section  pair of lt a26c1bd2bfcb: P2 M PI Mirror Section  pair of lt a26c1bd2bfcb
-- statement:
--   The P2 M PI Mirror Section  pair of lt a26c1bd2bfcb construction uses the P2 M PI Mirror Section  pair of lt a26c1bd2bfcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/MirrorDecompOf.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/MirrorDecompOf.lean#L50-L57

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
variable {k r : ℕ}

theorem P2M_PI_MirrorSection__pair_of_lt_a26c1bd2bfcb {m : ℕ} {P a : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det) (ha : P * a * P⁻¹ ∈ LTset m) :
    ∃ b, b ∈ UTset m ∧ bᴴ * P * a = P := by sorry

alias «PI».«MirrorSection₂».«pair_of_lt» := P2M_PI_MirrorSection__pair_of_lt_a26c1bd2bfcb
