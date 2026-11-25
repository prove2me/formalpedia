-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__conj_n_ea3c2f1eea26
-- name    : P2M_PI_MirrorSection__conj_n_ea3c2f1eea26
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:14.865119+00:00
-- url     : https://prove2.me/theorems/18957bb1-6c5e-4e47-b38c-e1100ed10fe0
-- title:
--   P2 M PI Mirror Section  conj n ea3c2f1eea26: P2 M PI Mirror Section  conj n ea3c2f1eea26
-- statement:
--   The P2 M PI Mirror Section  conj n ea3c2f1eea26 construction uses the P2 M PI Mirror Section  conj n ea3c2f1eea26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L249-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L249-L293

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
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
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem P2M_PI_MirrorSection__conj_n_ea3c2f1eea26 {z : Fin (2 * r + k + 1) → ℂ} {h n : B.Mat k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) :
    h⁻¹ * n * h ∈ Nset k r := by sorry

alias «PI».«MirrorSection₂».«conj_n» := P2M_PI_MirrorSection__conj_n_ea3c2f1eea26
