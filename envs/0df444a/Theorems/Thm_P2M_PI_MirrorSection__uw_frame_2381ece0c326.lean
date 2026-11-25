-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__uw_frame_2381ece0c326
-- name    : P2M_PI_MirrorSection__uw_frame_2381ece0c326
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:57:48.536534+00:00
-- url     : https://prove2.me/theorems/720b2181-71a9-455d-abab-a27e7c41d4af
-- title:
--   P2 M PI Mirror Section  uw frame 2381ece0c326: P2 M PI Mirror Section  uw frame 2381ece0c326
-- statement:
--   The P2 M PI Mirror Section  uw frame 2381ece0c326 construction uses the P2 M PI Mirror Section  uw frame 2381ece0c326 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/MirrorDecompOf.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/MirrorDecompOf.lean#L27-L38

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

theorem P2M_PI_MirrorSection__uw_frame_2381ece0c326 {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) :
    h * Ff k r z = Ff k r z := by sorry

alias «PI».«MirrorSection₂».«uw_frame» := P2M_PI_MirrorSection__uw_frame_2381ece0c326
